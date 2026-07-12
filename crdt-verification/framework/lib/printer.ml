open Format
open Ast

let pp_constant ppf = function
  | Cnone       -> pp_print_string ppf "()"
  | Cbool true  -> pp_print_string ppf "true"
  | Cbool false -> pp_print_string ppf "false"
  | Cstring s   -> fprintf ppf "%S" s
  | Cint n      -> pp_print_string ppf (Int64.to_string n)

let pp_w3_binop ppf = function
  | Badd -> pp_print_string ppf "+"
  | Bsub -> pp_print_string ppf "-"
  | Bmul -> pp_print_string ppf "*"
  | Bdiv -> pp_print_string ppf "/"
  | Beq  -> pp_print_string ppf "="
  | Bneq -> pp_print_string ppf "<>"
  | Blt  -> pp_print_string ppf "<"
  | Ble  -> pp_print_string ppf "<="
  | Bgt  -> pp_print_string ppf ">"
  | Bge  -> pp_print_string ppf ">="
  | Band -> pp_print_string ppf "/\\"
  | Bor  -> pp_print_string ppf "\\/"

let name_payload    = "payload"
let name_init_state = "init_state"
let name_create     = "create"
let name_equals     = "equals"
let name_make       = "make"

let strip_crdt_suffix name =
  match String.split_on_char '_' name with
  | base :: _ -> base
  | []        -> name

let uppercase_initials name =
  let buf = Buffer.create 4 in
  String.iter (fun c -> if c >= 'A' && c <= 'Z' then Buffer.add_char buf c) name;
  Buffer.contents buf

let derive_names mod_name =
  let base     = mod_name in
  let initials = uppercase_initials base in
  (initials ^ "Auxiliary", base, initials ^ "Aux")

let module_registry : (string, string * string) Hashtbl.t = Hashtbl.create 8

let aux_alias_of_module mod_name =
  match Hashtbl.find_opt module_registry mod_name with
  | Some (_, alias) -> Some alias
  | None -> None

let rewrite_qualified_name name =
  match String.split_on_char '.' name with
  | [mod_name; member] ->
      begin match aux_alias_of_module mod_name with
      | Some alias -> alias ^ "." ^ member
      | None -> name
      end
  | _ -> name

let rewrite_module_refs expr =
  let rec rw = function
    | TEvar v -> TEvar { v with v_name = rewrite_qualified_name v.v_name }
    | TEcall (fn, args)  ->
        TEcall ({ fn with fn_name = rewrite_qualified_name fn.fn_name }, List.map rw args)
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw e)) fields)
    | TEmatch (e, arms)  -> TEmatch (rw e, List.map (fun (n, b) -> (n, rw b)) arms)
    | other -> other
  in
  rw expr

let uses_int_int = ref false
let uses_min_max = ref false

let reset_uses () =
  uses_int_int := false;
  uses_min_max := false

let rec scan_ttp = function
  | TTInt | TTBool -> uses_int_int := true
  | TTMap (k, v) -> scan_ttp k; scan_ttp v
  | TTSet elem -> scan_ttp elem
  | TTRecord fields -> List.iter (fun (_, t) -> scan_ttp t) fields
  | _ -> ()

let rec scan_texpr = function
  | TEcall (fn, args) ->
      if fn.fn_name = "max" || fn.fn_name = "min" then begin
        uses_int_int := true;
        uses_min_max := true
      end;
      List.iter scan_texpr args
  | TEbinop (_, l, r) -> scan_texpr l; scan_texpr r
  | TErecord fields -> List.iter (fun (_, e) -> scan_texpr e) fields
  | TEmatch (e, arms) -> scan_texpr e;
      List.iter (fun (_, b) -> scan_texpr b) arms
  | _ -> ()

let scan_tmodl = function
  | TDtype (_, tp, _, _)      -> scan_ttp tp
  | TDval (fn, body, _) ->
      List.iter (fun v     -> scan_ttp v.v_tp) fn.fn_params;
      scan_ttp fn.fn_return;
      scan_texpr body

let rec pp_w3_ttp ppf = function
  | TTInt              -> pp_print_string ppf "int"
  | TTBool             -> pp_print_string ppf "bool"
  | TTMap (k, v)       -> fprintf ppf "map %a %a" pp_w3_ttp k pp_w3_ttp v
  | TTSet elem         -> fprintf ppf "fset %a" pp_w3_ttp elem
  | TTAbstract name    -> pp_print_string ppf name
  | TTRecord fields    -> fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, tp) -> fprintf ppf "%s: %a;" name pp_w3_ttp tp)) fields
  | TTInvariant names  -> pp_print_string ppf (String.concat " " names)
  | TTModuleRecord m   -> pp_print_string ppf m
  | TTVariant (_, _)   -> pp_print_string ppf "(* variant *)"

let rec pp_w3_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEbinop (op, l, r) ->
      fprintf ppf "@[<hv 1>%a@ %a@ %a@]" pp_w3_texpr l pp_w3_binop op pp_w3_texpr r
  | TEnot e            ->
      fprintf ppf "not %a" pp_w3_texpr_atom e
  | TEcall (fn, args)  ->
      fprintf ppf "@[<h>%s@ %a@]" fn.fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_w3_texpr_atom) args
  | TErecord fields    ->
      fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ";@ ")
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_w3_texpr e)) fields
  | TEmatch (e, arms)  ->
      fprintf ppf "@[<v>match %a with@ %a@ end@]" pp_w3_texpr e
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, body) ->
            match body with
            | TErecord _ ->
                fprintf ppf "@[<hv 2>| %s ->@ %a@]" name pp_w3_texpr body
            | _ ->
                fprintf ppf "@[<hv 2>| %s ->@ { %s = %a }@]" name name_payload pp_w3_texpr body)) arms

and pp_w3_texpr_atom ppf e = match e with
  | TEcst _ | TEvar _ -> pp_w3_texpr ppf e
  | _                 -> fprintf ppf "(%a)" pp_w3_texpr e

let pp_w3_tparams ppf params =
  let rec group = function
    | [] -> []
    | v :: rest ->
        let same, other = List.partition (fun u -> u.v_tp = v.v_tp) rest in
        (v :: same, v.v_tp) :: group other
  in
  pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
    (fun ppf (vs, tp) -> fprintf ppf "(%a: %a)"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ")
          (fun ppf v -> pp_print_string ppf v.v_name)) vs pp_w3_ttp tp) ppf (group params)

let pp_w3_uses ppf () =
  if !uses_int_int && !uses_min_max then
    fprintf ppf "use int.Int, int.MinMax@ @ "
  else if !uses_int_int then
    fprintf ppf "use int.Int@ @ "

let is_bool_ttp = function TTBool -> true | _ -> false

let pp_w3_equals_predicate ppf () =
  fprintf ppf "@[<v>predicate %s (a b: t)@ = compare a b /\\ compare b a@]" name_equals

let interface_fn_names intfs =
  List.filter_map (function
    | Ifunc (id, _, _) -> Some id.id
    | Itype _ | Iaxiom _ -> None) intfs

let is_two_module_interface intfs =
  let fns = interface_fn_names intfs in
  List.mem "merge" fns && List.mem "compare" fns

let payload_param_names fn =
  List.filter_map (fun v ->
    if v.v_tp = TTModuleRecord name_payload then Some v.v_name
    else None) fn.fn_params

let rec map_texpr f expr =
  let descended = match expr with
    | TEbinop (op, l, r) -> TEbinop (op, map_texpr f l, map_texpr f r)
    | TEnot e            -> TEnot (map_texpr f e)
    | TEcall (fn, args)  -> TEcall (fn, List.map (map_texpr f) args)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, map_texpr f e)) fields)
    | TEmatch (e, arms)  -> TEmatch (map_texpr f e, List.map (fun (n, b) -> (n, map_texpr f b)) arms)
    | other              -> other
  in
  f descended

let rewrite_texpr_for_aux payload_vars body =
  map_texpr (function
    | TEvar v when List.mem v.v_name payload_vars ->
        TEvar { v with v_name = v.v_name ^ ".payload" }
    | other -> other) body

let pp_w3_aux_decl ppf = function
  | TDtype (name, TTVariant (_, ctors), _, _) ->
      fprintf ppf "@[type %s =@ %a@]" name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " | ") pp_print_string) ctors

  | TDtype ("payload", tp, _, _) ->
      fprintf ppf "@[type %s = %a@]" name_payload pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = { %s: %a; }@]" name_payload pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let function get_payload (a: t) : %s@ = a.%s@]" name_payload name_payload

  | TDtype (name, tp, _, _) ->
      fprintf ppf "@[type %s = %a@]" name pp_w3_ttp tp

  | TDval ({ fn_name = "init_state"; _ }, body, _) ->
      fprintf ppf "@[<v 2>let ghost function %s () : t@ = { %s = %a }@]"
        name_create name_payload pp_w3_texpr body

  | TDval (fn, body, _) ->
      let rewrite_param v =
        if v.v_tp = TTModuleRecord name_payload then { v with v_tp = TTModuleRecord "t" }
        else v
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let pvars = payload_param_names fn in
      let ret =
        if fn.fn_return = TTModuleRecord name_payload then TTModuleRecord "t"
        else fn.fn_return
      in
      let rewritten = rewrite_texpr_for_aux pvars body in
      let pp_aux_match_arm ppf (name, arm_body) =
        match arm_body with
        | TErecord _ ->
            fprintf ppf "@[<hv 2>| %s ->@ %a@]" name pp_w3_texpr arm_body
        | _ ->
            fprintf ppf "@[<hv 2>| %s ->@ { %s = %a }@]" name name_payload pp_w3_texpr arm_body
      in
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[<v 2>predicate %s %a@ = %a@]"
          fn.fn_name pp_w3_tparams tparams pp_w3_texpr rewritten
      else begin
        match rewritten with
        | TEmatch (e, arms) ->
            fprintf ppf "@[<v 2>function %s %a : %a@ = @[<v>match %a with@ %a@ end@]@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret pp_w3_texpr e
              (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") pp_aux_match_arm) arms
        | _ ->
            fprintf ppf "@[<v 2>let function %s %a : %a@ = { %s = %a }@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret name_payload pp_w3_texpr rewritten
      end

let translate_fn_name fn_name =
  match String.split_on_char '.' fn_name with
  | [m; f] when Hashtbl.mem module_registry m ->
      let (_, alias) = Hashtbl.find module_registry m in
      let f' = if f = name_init_state then name_create else f in
      alias ^ "." ^ f'
  | _ ->
      if fn_name = name_init_state then name_create else fn_name

let pp_w3_auxiliary ppf aux_mod intfs decls =
  reset_uses ();
  List.iter scan_tmodl decls;
  let aux_only_exclude = List.filter_map (function
    | Ifunc (id, _, _) when id.id = name_equals -> Some id.id
    | _ -> None) intfs in
  let aux_decls = List.filter (function
    | TDval (fn, _, _) -> not (List.mem fn.fn_name aux_only_exclude)
    | _ -> true) decls in
  let variant_decls = List.filter (function TDtype (_, TTVariant _, _, _) -> true | _ -> false) aux_decls in
  let other_decls = List.filter (function TDtype (_, TTVariant _, _, _) -> false | _ -> true) aux_decls in
  let ordered = variant_decls @ other_decls in
  fprintf ppf "@[<v 2>module %s@ @ %a%a@]@ @ end@ " aux_mod pp_w3_uses ()
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_aux_decl) ordered

let pp_w3_main_decl ppf (aux_alias, _payload_tp, tmodl) =
  match tmodl with
  | TDtype ("payload", _, _, _) ->
      fprintf ppf "@[type %s = %s.%s@]" name_payload aux_alias name_payload;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = %s.t@]" aux_alias

  | TDtype (name, _, _, _) ->
      fprintf ppf "@[type %s = %s.%s@]" name aux_alias name

  | TDval ({ fn_name = "init_state"; _ }, _, _) ->
      fprintf ppf "@[<v 2>let function get_payload (a: t) : %a@ = %s.get_payload a@]"
        pp_w3_ttp _payload_tp aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let ghost function %s () : t@ = %s.%s ()@]"
        name_create aux_alias name_create

  | TDval ({ fn_name = "equals"; _ }, _, _) ->
      pp_w3_equals_predicate ppf ()

  | TDval (fn, _, _) ->
      let rewrite_param v =
        if v.v_tp = TTModuleRecord name_payload then { v with v_tp = TTModuleRecord "t" }
        else v
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let param_names ppf ps =
        pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
          (fun ppf v -> pp_print_string ppf v.v_name) ppf ps
      in
      let ret =
        if fn.fn_return = TTModuleRecord name_payload then TTModuleRecord "t"
        else fn.fn_return
      in
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[<v 2>predicate %s %a@ = %s.%s %a@]"
          fn.fn_name pp_w3_tparams tparams aux_alias fn.fn_name param_names tparams
      else
        fprintf ppf "@[<v 2>let function %s %a : %a@ = %s.%s %a@]"
          fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret aux_alias fn.fn_name param_names tparams

let pp_w3_main ppf (main_mod, sig_name, aux_mod, aux_alias, intfs, decls) =
  reset_uses ();
  List.iter scan_tmodl decls;
  let payload_tp = List.fold_left (fun acc d -> match d with
    | TDtype ("payload", tp, _, _) -> tp
    | _ -> acc) TTInt decls in
  let intf_fns = interface_fn_names intfs in
  let interface_decls = List.filter (function
    | TDtype _ -> true
    | TDval (fn, _, _) -> List.mem fn.fn_name intf_fns) decls in
  fprintf ppf "@[<v 2>module %s : %s@ @ %ause %s as %s@ @ %a@]@ @ end@ "
    main_mod sig_name
    pp_w3_uses ()
    aux_mod aux_alias
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
      (fun ppf d -> pp_w3_main_decl ppf (aux_alias, payload_tp, d))) interface_decls

let get_set_elem_type decls =
  List.fold_left (fun acc d -> match d with
    | TDtype ("payload", TTSet elem_tp, _, _) -> Some elem_tp
    | TDtype ("payload", TTRecord fields, _, _) ->
        List.fold_left (fun a (_, ftp) -> match a, ftp with
          | None, TTSet elem_tp -> Some elem_tp
          | _ -> a) acc fields
    | _ -> acc) None decls

let get_set_record_fields decls =
  List.fold_left (fun acc d -> match d with
    | TDtype ("payload", TTRecord fields, _, _)
      when List.exists (fun (_, tp) -> match tp with TTSet _ -> true | _ -> false) fields ->
        Some fields
    | _ -> acc) None decls

let w3_set_fn = function
  | "set.empty"    -> "Fset.empty"
  | "set.add"      -> "Fset.add"
  | "set.union"    -> "Fset.union"
  | "set.contains" -> "Fset.mem"
  | "set.subset"   -> "Fset.subset"
  | other          -> other

let rec rw_w3_set_expr = function
  | TEcall (fn, args) ->
      TEcall ({ fn with fn_name = w3_set_fn fn.fn_name },
              List.map rw_w3_set_expr args)
  | TEvar v ->
      TEvar { v with v_name = w3_set_fn v.v_name }
  | TEnot e            -> TEnot (rw_w3_set_expr e)
  | TEbinop (op, l, r) -> TEbinop (op, rw_w3_set_expr l, rw_w3_set_expr r)
  | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw_w3_set_expr e)) fields)
  | TEmatch (e, arms)  -> TEmatch (rw_w3_set_expr e,
                            List.map (fun (n, b) -> (n, rw_w3_set_expr b)) arms)
  | other -> other

let pp_w3_set_auxiliary ppf (aux_mod, elem_tp, decls) =
  let elem_name = match elem_tp with
    | TTAbstract n -> n
    | TTModuleRecord n -> n
    | _ -> "elem"
  in
  let set_record_fields = get_set_record_fields decls in
  let is_record_set = set_record_fields <> None in
  let rewrite_param v = match v.v_tp with
    | TTModuleRecord p when p = name_payload -> { v with v_tp = TTModuleRecord "t 'v" }
    | TTAbstract _ -> { v with v_tp = TTModuleRecord "'v" }
    | TTModuleRecord n when n = elem_name -> { v with v_tp = TTModuleRecord "'v" }
    | _ -> v
  in
  fprintf ppf "@[<v 2>module %s@ @ " aux_mod;
  fprintf ppf "use set.Fset@ @ ";
  fprintf ppf "type %s 'v = fset 'v@ @ " name_payload;
  if is_record_set then begin
    let fields = Option.get set_record_fields in
    fprintf ppf "type t 'v = { %a }@ @ "
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
        (fun ppf (n, _) -> fprintf ppf "%s: fset 'v" n)) fields;
    let payload_fn_name = String.lowercase_ascii (String.sub aux_mod 0 3) ^ "_payload" in
    fprintf ppf "@[<v 2>val function %s (s1 s2: fset 'v) : fset 'v@ ensures { result = Fset.diff s1 s2 }@]@ @ "
      payload_fn_name;
    fprintf ppf "@[<v 2>let function get_payload (t: t 'v) : fset 'v@ = %s %a@]@ @ "
      payload_fn_name
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ")
        (fun ppf (n, _) -> fprintf ppf "t.%s" n)) fields;
    fprintf ppf "@[<v 2>let ghost function %s () : t 'v@ = { %a }@]@ @ "
      name_create
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
        (fun ppf (n, _) -> fprintf ppf "%s = Fset.empty" n)) fields;
    List.iter (function
      | TDtype _ -> ()
      | TDval ({ fn_name = "init_state"; _ }, _, _) -> ()
      | TDval ({ fn_name = "equals"; _ }, _, _) -> ()
      | TDval (fn, body, _) ->
          let pvars = payload_param_names fn in
          let body' = rw_w3_set_expr (rewrite_texpr_for_aux pvars body) in
          let tparams = List.map rewrite_param fn.fn_params in
          if is_bool_ttp fn.fn_return then
            fprintf ppf "@[<v 2>predicate %s %a@ = %a@]@ @ "
              fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
          else
            fprintf ppf "@[<v 2>function %s %a : t 'v@ = %a@]@ @ "
              fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
    ) decls
  end else begin
    fprintf ppf "type t 'v = { %s: fset 'v; }@ @ " name_payload;
    fprintf ppf "@[<v 2>let function get_payload (t: t 'v) : fset 'v@ = t.%s@]@ @ " name_payload;
    fprintf ppf "@[<v 2>let ghost function %s () : t 'v@ = { %s = Fset.empty }@]@ @ "
      name_create name_payload;
    List.iter (function
      | TDtype _ -> ()
      | TDval ({ fn_name = "init_state"; _ }, _, _) -> ()
      | TDval ({ fn_name = "equals"; _ }, _, _) -> ()
      | TDval (fn, body, _) ->
          let pvars = payload_param_names fn in
          let body' = rw_w3_set_expr (rewrite_texpr_for_aux pvars body) in
          let tparams = List.map rewrite_param fn.fn_params in
          if is_bool_ttp fn.fn_return then
            fprintf ppf "@[<v 2>predicate %s %a@ = %a@]@ @ "
              fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
          else
            fprintf ppf "@[<v 2>function %s %a : t 'v@ = { %s = %a }@]@ @ "
              fn.fn_name pp_w3_tparams tparams name_payload pp_w3_texpr body'
    ) decls
  end;
  fprintf ppf "@]@ @ end@ "

let pp_w3_set_main ppf (main_mod, sig_name, aux_mod, aux_alias, elem_tp, intfs, decls) =
  let intf_fns = interface_fn_names intfs in
  let elem_name = match elem_tp with
    | TTAbstract n -> n
    | TTModuleRecord n -> n
    | _ -> "elem"
  in
  fprintf ppf "@[<v 2>module %s : %s@ @ " main_mod sig_name;
  fprintf ppf "use %s as %s@ @ " aux_mod aux_alias;
  fprintf ppf "@[type %s@]@ @ " elem_name;
  fprintf ppf "@[type %s = %s.%s %s@]@ @ " name_payload aux_alias name_payload elem_name;
  fprintf ppf "@[type t = %s.t %s@]@ @ " aux_alias elem_name;
  (match List.find_opt (function TDval ({ fn_name = "init_state"; _ }, _, _) -> true | _ -> false) decls with
   | Some _ ->
       fprintf ppf "@[<v 2>let function get_payload (a: t) : %s@ = %s.get_payload a@]@ @ "
         name_payload aux_alias;
       fprintf ppf "@[<v 2>let ghost function %s () : t@ = %s.%s ()@]@ @ "
         name_create aux_alias name_create
   | None -> ());
  List.iter (function
    | TDtype _ -> ()
    | TDval ({ fn_name = "init_state"; _ }, _, _) -> ()
    | TDval ({ fn_name = "equals"; _ }, _, _) ->
        pp_w3_equals_predicate ppf ();
        fprintf ppf "@ @ "
    | TDval (fn, _, _) ->
        let tparams = List.map (fun v -> match v.v_tp with
          | TTModuleRecord p when p = name_payload -> { v with v_tp = TTModuleRecord "t" }
          | TTAbstract _ -> { v with v_tp = TTModuleRecord elem_name }
          | TTModuleRecord n when n = elem_name -> v
          | _ -> v) fn.fn_params in
        let param_names ppf ps =
          pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
            (fun ppf v -> pp_print_string ppf v.v_name) ppf ps
        in
        let _ = intf_fns in
        if is_bool_ttp fn.fn_return then
          fprintf ppf "@[<v 2>predicate %s %a@ = %s.%s %a@]@ @ "
            fn.fn_name pp_w3_tparams tparams aux_alias fn.fn_name param_names tparams
        else
          fprintf ppf "@[<v 2>function %s %a : t@ = %s.%s %a@]@ @ "
            fn.fn_name pp_w3_tparams tparams aux_alias fn.fn_name param_names tparams
  ) decls;
  fprintf ppf "@]@ @ end@ "

let vfx_class_name mod_name = mod_name

let rec pp_vfx_texpr_simple ppf = function
  | TEvar v -> Format.pp_print_string ppf v.v_name
  | TEcall (fn, []) -> Format.fprintf ppf "%s()" fn.fn_name
  | TEcall (fn, args) ->
      Format.fprintf ppf "%s(%a)" fn.fn_name
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
           pp_vfx_texpr_simple) args
  | _ -> Format.pp_print_string ppf "?"

let rec rw_vfx_set_expr = function
  | TEcall ({ fn_name = "set.add"; _ }, [elem; col]) ->
      let col'  = rw_vfx_set_expr col  in
      let elem' = rw_vfx_set_expr elem in
      TEvar { v_name = Format.asprintf "%a.add(%a)" pp_vfx_texpr_simple col' pp_vfx_texpr_simple elem';
              v_tp   = TTBool }
  | TEcall ({ fn_name = "set.union"; _ }, [a; b]) ->
      let a' = rw_vfx_set_expr a and b' = rw_vfx_set_expr b in
      TEvar { v_name = Format.asprintf "%a.union(%a)" pp_vfx_texpr_simple a' pp_vfx_texpr_simple b';
              v_tp   = TTBool }
  | TEcall ({ fn_name = "set.contains"; _ }, [elem; col]) ->
      let col'  = rw_vfx_set_expr col  in
      let elem' = rw_vfx_set_expr elem in
      TEvar { v_name = Format.asprintf "%a.contains(%a)" pp_vfx_texpr_simple col' pp_vfx_texpr_simple elem';
              v_tp   = TTBool }
  | TEcall ({ fn_name = "set.subset"; _ }, [a; b]) ->
      let a' = rw_vfx_set_expr a and b' = rw_vfx_set_expr b in
      TEvar { v_name = Format.asprintf "%a.subsetOf(%a)" pp_vfx_texpr_simple a' pp_vfx_texpr_simple b';
              v_tp   = TTBool }
  | TEcall ({ fn_name = "set.empty"; _ }, _) | TEvar { v_name = "set.empty"; _ } ->
      TEvar { v_name = "set.empty"; v_tp = TTBool }
  | TEnot e            -> TEnot (rw_vfx_set_expr e)
  | TEbinop (op, l, r) -> TEbinop (op, rw_vfx_set_expr l, rw_vfx_set_expr r)
  | TEcall (fn, args)  -> TEcall (fn, List.map rw_vfx_set_expr args)
  | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw_vfx_set_expr e)) fields)
  | TEmatch (e, arms)  -> TEmatch (rw_vfx_set_expr e,
                            List.map (fun (n, b) -> (n, rw_vfx_set_expr b)) arms)
  | other -> other

let get_composite_source decls =
  List.fold_left (fun acc d -> match d, acc with
    | TDtype ("payload", TTRecord fields, _, _), None ->
        let ext_fields = List.filter_map (fun (_, tp) ->
          match tp with
          | TTModuleRecord s when String.contains s '.' ->
              let parts = String.split_on_char '.' s in
              begin match parts with
              | [mod_name; _] -> Some mod_name
              | _ -> None
              end
          | _ -> None) fields in
        begin match ext_fields with
        | mod_name :: _ -> Some mod_name
        | [] -> None
        end
    | _ -> acc) None decls

let payload_field_name mod_name =
  let base = strip_crdt_suffix mod_name in
  let initials = String.lowercase_ascii (uppercase_initials base) in
  "payload_" ^ initials

let pp_w3_axiom ppf (prop, func) =
  match prop with
  | "commutative" ->
      fprintf ppf "axiom %s_commutative: forall a b: t.@ " func;
      fprintf ppf "  equals (%s a b) (%s b a)" func func
  | "idempotent" ->
      fprintf ppf "axiom %s_idempotent: forall a: t.@ " func;
      fprintf ppf "  equals (%s a a) a" func
  | "associative" ->
      fprintf ppf "axiom %s_associative: forall a, b, c: t.@ " func;
      fprintf ppf "  equals (%s (%s a b) c) (%s a (%s b c))" func func func func
  | "equivalence" ->
      fprintf ppf "axiom %s_correct: forall a, b: t.@ " func;
      fprintf ppf "  equals a b <-> a = b"
  | "op_commutative" ->
      fprintf ppf "axiom op_commutative: forall o1 o2: operation, a: t.@ ";
      fprintf ppf "  equals (%s o2 (%s o1 a)) (%s o1 (%s o2 a))" func func func func
  | other ->
      fprintf ppf "(* unknown axiom: %s(%s) *)" other func

let pp_w3_axioms ppf intfs =
  let axioms = List.filter_map (function
    | Iaxiom (prop, func) -> Some (prop.id, func.id)
    | _ -> None) intfs in
  if axioms <> [] then begin
    fprintf ppf "@ @ ";
    pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
      (fun ppf (prop, func) -> pp_w3_axiom ppf (prop, func)) ppf axioms
  end

let resolve_intf_tp = function
  | Tcst { id = "boolean"; _ }  -> TTBool
  | Tcst { id = "payload"; _ }  -> TTModuleRecord "t"
  | Tcst { id = other; _ } -> TTModuleRecord other
  | _                           -> TTModuleRecord "t"

let pp_w3_intf_decl ppf = function
  | Itype id ->
      fprintf ppf "@[type %s@]" id.id
  | Ifunc (id, [], _tp) ->
      if id.id = name_init_state then
        fprintf ppf "@[val ghost function %s () : t@]" name_create
      else
        fprintf ppf "@[val function %s (t: t) : %s@]" id.id name_payload
  | Ifunc (id, params, tp) ->
      let pp_param_type ppf (_, pty) =
        match resolve_intf_tp pty with
        | TTModuleRecord s -> pp_print_string ppf s
        | other           -> pp_w3_ttp ppf other
      in
      if is_bool_ttp (resolve_intf_tp tp) then
        fprintf ppf "@[predicate %s %a@]" id.id
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_param_type) params
      else
        fprintf ppf "@[function %s %a : t@]" id.id
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_param_type) params
  | Iaxiom _ -> ()

let pp_w3_interface ppf (name, intfs) =
  let payload_types = List.filter (function
    | Itype id -> id.id = name_payload
    | _ -> false) intfs in
  let other_types = List.filter (function
    | Itype id -> id.id <> name_payload
    | _ -> false) intfs in
  let funcs = List.filter (function
    | Ifunc (id, _, _) -> id.id <> name_equals && id.id <> name_init_state
    | _ -> false) intfs in
  fprintf ppf "@[<v 2>module %s@ @ " name;
  pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
    pp_w3_intf_decl ppf payload_types;
  fprintf ppf "@ @ @[type t@]@ @ ";
  if other_types <> [] then begin
    pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
      pp_w3_intf_decl ppf other_types;
    fprintf ppf "@ @ "
  end;
  fprintf ppf "@[val ghost function %s () : t@]@ @ " name_create;
  fprintf ppf "@[val function get_payload (a: t) : %s@]@ @ " name_payload;
  pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
    pp_w3_intf_decl ppf funcs;
  fprintf ppf "@ @ ";
  pp_w3_equals_predicate ppf ();
  pp_w3_axioms ppf intfs;
  fprintf ppf "@]@ @ end@ "

let pp_w3_composite ppf (main_mod, sig_name, intfs, decls) =
  let source_mod = match get_composite_source decls with
    | Some m -> m
    | None -> failwith "pp_w3_composite: no composite source found"
  in
  let (aux_mod, _, aux_alias) = derive_names source_mod in
  let payload_fn = payload_field_name main_mod in
  reset_uses ();
  List.iter scan_tmodl decls;
  uses_int_int := true;

  let payload_fields, inv_opt, init_body =
    List.fold_left (fun (pf, inv, ib) d -> match d with
      | TDtype (n, TTRecord fields, i, _) when n = name_payload -> (fields, i, ib)
      | TDtype (n, _, i, _)              when n = name_payload -> (pf, i, ib)
      | TDval ({ fn_name; _ }, body, _)  when fn_name = name_init_state -> (pf, inv, Some body)
      | _ -> (pf, inv, ib))
    ([], None, None) decls
  in

  let intf_fns = interface_fn_names intfs in

  let rw_expr = map_texpr (function
    | TEvar v ->
        TEvar { v with v_name =
          match String.split_on_char '.' v.v_name with
          | [m; f] when Hashtbl.mem module_registry m ->
              let (_, alias) = Hashtbl.find module_registry m in alias ^ "." ^ f
          | _ -> v.v_name }
    | TEcall (fn, args) ->
        TEcall ({ fn with fn_name = translate_fn_name fn.fn_name }, args)
    | TErecord fields ->
        TErecord (List.map (fun (n, e) ->
          let n' = if n = name_payload then payload_fn else n in (n', e)) fields)
    | other -> other)
  in

  let rw_inv_expr = map_texpr (function
    | TEvar v ->
        TEvar { v with v_name =
          match String.split_on_char '.' v.v_name with
          | [_var; p] when p = name_payload -> payload_fn
          | [_var; field] -> field
          | _ -> v.v_name }
    | TEcall (fn, args) ->
        TEcall ({ fn with fn_name = rewrite_qualified_name fn.fn_name }, args)
    | other -> other)
  in

  let rw_inv_field_access expr =
    let ext_fields = List.filter_map (fun (name, tp) ->
      match tp with
      | TTModuleRecord s when String.contains s '.' -> Some name
      | _ -> None) payload_fields in
    map_texpr (function
      | TEvar v when List.mem v.v_name ext_fields ->
          let get_fn = { fn_name = aux_alias ^ ".get_payload";
                        fn_params = []; fn_return = TTInt } in
          TEcall (get_fn, [TEvar v])
      | other -> other) expr
  in

  let rw_init_field (name, e) =
    let fname = if name = name_payload then payload_fn else name in
    (fname, rw_expr e)
  in

  fprintf ppf "@[<v 2>module %s : %s@ @ use int.Int@ use %s as %s@ @ "
    main_mod sig_name aux_mod aux_alias;
  fprintf ppf "@[type %s = int@]@ @ " name_payload;

  fprintf ppf "type t = { %a }@ "
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
      (fun ppf (name, tp) ->
        let tp' = match tp with
          | TTModuleRecord s when String.contains s '.' ->
              TTModuleRecord (aux_alias ^ ".t")
          | other -> other
        in
        let fname = if name = name_payload then payload_fn else name in
        let tp'' = if name = name_payload then TTModuleRecord name_payload else tp' in
        fprintf ppf "%s: %a" fname pp_w3_ttp tp'')) payload_fields;

  begin match inv_opt with
  | Some (_inv_fn, inv_body) ->
      let body = rw_inv_field_access (rw_inv_expr inv_body) in
      fprintf ppf "  invariant { %a }@ " pp_w3_texpr body
  | None -> ()
  end;

  begin match init_body with
  | Some (TErecord fields) ->
      fprintf ppf "  by { %a }@ @ "
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
          (fun ppf f -> let (n, e) = rw_init_field f in
            fprintf ppf "%s = %a" n pp_w3_texpr e))
        fields
  | _ -> fprintf ppf "@ @ "
  end;

  fprintf ppf "@[<v 2>let function get_payload (a: t) : %s@ = a.%s@]@ @ "
    name_payload payload_fn;

  begin match init_body with
  | Some (TErecord fields) ->
      fprintf ppf "@[<v 2>let ghost function %s () : t@ = { %a }@]@ @ "
        name_create
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
          (fun ppf f -> let (n, e) = rw_init_field f in
            fprintf ppf "%s = %a" n pp_w3_texpr e)) fields
  | _ -> ()
  end;

  let make_decl = List.find_opt
    (function TDval ({ fn_name; _ }, _, _) -> fn_name = name_make | _ -> false) decls in
  begin match make_decl with
  | Some (TDval (fn, body, _)) ->
      let rewrite_param v =
        match v.v_tp with
        | TTModuleRecord s when String.contains s '.' ->
            { v with v_tp = TTModuleRecord (aux_alias ^ ".t") }
        | other -> { v with v_tp = other }
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let body' = rw_expr body in
      fprintf ppf "@[<v 2>let function %s %a : t@ = %a@]@ @ "
        name_make pp_w3_tparams tparams pp_w3_texpr body'
  | _ -> ()
  end;

  let other_decls = List.filter (function
    | TDtype _ -> false
    | TDval ({ fn_name; _ }, _, _) ->
        fn_name <> name_init_state && fn_name <> name_make) decls in

  let pp_composite_decl ppf = function
    | TDval ({ fn_name = "equals"; _ }, _, _) ->
        pp_w3_equals_predicate ppf ()
    | TDval (fn, body, _) ->
        let rewrite_param v =
          match v.v_tp with
          | TTModuleRecord p when p = name_payload -> { v with v_tp = TTModuleRecord "t" }
          | other -> { v with v_tp = other }
        in
        let tparams = List.map rewrite_param fn.fn_params in
        let body' = rw_expr body in
        if is_bool_ttp fn.fn_return then
          fprintf ppf "@[<v 2>predicate %s %a@ = %a@]"
            fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
        else begin
          let is_pure = match body' with
            | TEmatch _ -> true
            | TEcall ({ fn_name; _ }, _) when fn_name = name_make -> true
            | _ -> false
          in
          if is_pure then
            fprintf ppf "@[<v 2>function %s %a : t@ = %a@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
          else
            fprintf ppf "@[<v 2>let function %s %a : t@ = %a@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
        end
    | _ -> ()
  in

  let intf_decls = List.filter (function
    | TDval (fn, _, _) -> List.mem fn.fn_name intf_fns | _ -> false) other_decls in
  let extra_decls = List.filter (function
    | TDval (fn, _, _) -> not (List.mem fn.fn_name intf_fns) | _ -> false) other_decls in
  let ordered = extra_decls @ intf_decls in

  pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
    pp_composite_decl ppf ordered;
  fprintf ppf "@]@ @ end@ "

let pp_w3_tdef ppf = function
  | TDefInterface (name, _proof, intfs) ->
      pp_w3_interface ppf (name, intfs)
  | TDefModule (name, sig_name, intfs, decls) ->
      let (aux_mod, main_mod, aux_alias) = derive_names name in
      Hashtbl.replace module_registry name (aux_mod, aux_alias);
      let set_elem_tp  = get_set_elem_type decls in
      let is_composite = get_composite_source decls <> None in
      if set_elem_tp <> None then begin
        let elem_tp = Option.get set_elem_tp in
        pp_w3_set_auxiliary ppf (aux_mod, elem_tp, decls);
        fprintf ppf "@ ";
        pp_w3_set_main ppf (main_mod, sig_name, aux_mod, aux_alias, elem_tp, intfs, decls)
      end else if is_composite then begin
        pp_w3_composite ppf (main_mod, sig_name, intfs, decls)
      end else if is_two_module_interface intfs then begin
        pp_w3_auxiliary ppf aux_mod intfs decls;
        fprintf ppf "@ ";
        pp_w3_main ppf (main_mod, sig_name, aux_mod, aux_alias, intfs, decls)
      end else begin
        reset_uses ();
        List.iter scan_tmodl decls;
        let variant_decls = List.filter (function TDtype (_, TTVariant _, _, _) -> true | _ -> false) decls in
        let other_decls = List.filter (function TDtype (_, TTVariant _, _, _) -> false | _ -> true) decls in
        let ordered = variant_decls @ other_decls in
        fprintf ppf "@[<v 2>module %s : %s@ @ %a%a@]@ @ end@ "
          main_mod sig_name
          pp_w3_uses ()
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
            (fun ppf d -> match d with
              | TDval ({ fn_name; _ }, _, _) when fn_name = name_equals ->
                  pp_w3_equals_predicate ppf ()
              | _ -> pp_w3_aux_decl ppf d)) ordered
      end

let pp_w3_tfile ppf defs =
  fprintf ppf "@[<v>%a@]@."
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") pp_w3_tdef) defs

let print_w3_tfile tfile = pp_w3_tfile std_formatter tfile
let write_w3_tfile fmt tfile = pp_w3_tfile fmt tfile

let capitalise s =
  if String.length s = 0 then s
  else String.make 1 (Char.uppercase_ascii s.[0]) ^ String.sub s 1 (String.length s - 1)

let axiom_to_proof_name prop func = func ^ capitalise prop

let pp_vfx_proof ppf (prop, func) =
  match prop with
  | "commutative" ->
      fprintf ppf "  proof %s {@ " (axiom_to_proof_name prop func);
      fprintf ppf "    forall (x: T, y: T) {@ ";
      fprintf ppf "      (x.reachable() && y.reachable() && x.compatible(y)) =>: {@ ";
      fprintf ppf "        x.%s(y).equals(y.%s(x)) &&@ " func func;
      fprintf ppf "        x.%s(y).reachable()@ " func;
      fprintf ppf "      }@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "idempotent" ->
      fprintf ppf "  proof %s {@ " (axiom_to_proof_name prop func);
      fprintf ppf "    forall (x: T) {@ ";
      fprintf ppf "      x.reachable() =>: x.%s(x).equals(x)@ " func;
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "associative" ->
      fprintf ppf "  proof %s {@ " (axiom_to_proof_name prop func);
      fprintf ppf "    forall (x: T, y: T, z: T) {@ ";
      fprintf ppf "      ( x.reachable() && y.reachable() && z.reachable() &&@ ";
      fprintf ppf "          x.compatible(y) && x.compatible(z) && y.compatible(z) ) =>: {@ ";
      fprintf ppf "        x.%s(y).%s(z).equals(x.%s(y.%s(z))) &&@ " func func func func;
      fprintf ppf "        x.%s(y).%s(z).reachable()@ " func func;
      fprintf ppf "      }@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "equivalence" ->
      fprintf ppf "  proof %s {@ " (axiom_to_proof_name prop func);
      fprintf ppf "    forall (x: T, y: T) {@ ";
      fprintf ppf "      x.equals(y) == (x == y)@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "op_commutative" ->
      fprintf ppf "  proof op_commutative {@ ";
      fprintf ppf "    forall (s1: T, s2: T, s3: T, x: Op, y: Op) {@ ";
      fprintf ppf "      val msg1 = s1.prepare(x)@ ";
      fprintf ppf "      val msg2 = s2.prepare(y)@ ";
      fprintf ppf "      ( s1.reachable() && s2.reachable() && s3.reachable() &&@ ";
      fprintf ppf "          s1.enabledSrc(x) && s2.enabledSrc(y) &&@ ";
      fprintf ppf "              s1.compatible(msg1, msg2) ) =>: {@ ";
      fprintf ppf "        s3.tryEffect(msg1).tryEffect(msg2).equals(s3.tryEffect(msg2).tryEffect(msg1)) &&@ ";
      fprintf ppf "        s3.tryEffect(msg1).tryEffect(msg2).reachable()@ ";
      fprintf ppf "      }@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | _ -> fprintf ppf "  (* unknown proof for axiom: %s(%s) *)" prop func

let pp_vfx_is_a_cvrdt ppf () =
  fprintf ppf "  proof is_a_CvRDT {@ ";
  fprintf ppf "    forall(x: T, y: T, z: T) {@ ";
  fprintf ppf "      ( x.reachable() && y.reachable() && z.reachable() &&@ ";
  fprintf ppf "          x.compatible(y) && x.compatible(z) && y.compatible(z) ) =>: {@ ";
  fprintf ppf "        x.merge(x).equals(x) &&@ ";
  fprintf ppf "        x.merge(y).equals(y.merge(x)) &&@ ";
  fprintf ppf "        x.merge(y).merge(z).equals(x.merge(y.merge(z))) &&@ ";
  fprintf ppf "        x.merge(y).reachable() &&@ ";
  fprintf ppf "        x.merge(y).merge(z).reachable() &&@ ";
  fprintf ppf "        x.compatible(y) == y.compatible(x)@ ";
  fprintf ppf "      }@ ";
  fprintf ppf "    }@ ";
  fprintf ppf "  }"

let pp_vfx_is_a_cmrdt ppf () =
  fprintf ppf "  proof is_a_CmRDT {@ ";
  fprintf ppf "    forall (s1: T, s2: T, s3: T, x: Op, y: Op) {@ ";
  fprintf ppf "      val msg1 = s1.prepare(x)@ ";
  fprintf ppf "      val msg2 = s2.prepare(y)@ ";
  fprintf ppf "      ( s1.reachable() && s2.reachable() && s3.reachable() &&@ ";
  fprintf ppf "          s1.enabledSrc(x) && s2.enabledSrc(y) &&@ ";
  fprintf ppf "              s1.compatible(msg1, msg2) && s1.compatibleS(s2) && s1.compatibleS(s3) && s2.compatibleS(s3) ) =>: {@ ";
  fprintf ppf "        s3.tryEffect(msg1).tryEffect(msg2).equals(s3.tryEffect(msg2).tryEffect(msg1)) &&@ ";
  fprintf ppf "        s3.tryEffect(msg1).reachable() &&@ ";
  fprintf ppf "        s3.tryEffect(msg2).reachable() &&@ ";
  fprintf ppf "        s3.tryEffect(msg1).tryEffect(msg2).reachable()@ ";
  fprintf ppf "      }@ ";
  fprintf ppf "    }@ ";
  fprintf ppf "  }"

let pp_vfx_intf_fn ppf = function
  | Itype _ | Iaxiom _ -> ()
  | Ifunc (id, _, tp) ->
      if id.id = "init_state" then ()
      else if id.id = "equals" then begin
        fprintf ppf "@ ";
        fprintf ppf "  def equals(that: T): Boolean =@ ";
        fprintf ppf "    this.asInstanceOf[T].compare(that) && that.compare(this.asInstanceOf[T])@ "
      end else if is_bool_ttp (resolve_intf_tp tp) then begin
        fprintf ppf "@ ";
        fprintf ppf "  def %s(that: T): Boolean@ " id.id
      end else begin
        fprintf ppf "@ ";
        fprintf ppf "  def %s(that: T): T@ " id.id
      end

let is_cvrdt_interface intfs =
  List.exists (function Ifunc (id, _, _) -> id.id = "merge" | _ -> false) intfs

let pp_vfx_cvrdt ppf (name, intfs) =
  let fns = List.filter (function Ifunc _ -> true | _ -> false) intfs in
  fprintf ppf "@[<v>trait %s[T <: %s[T]] {@ @ " name name;
  fprintf ppf "  def reachable(): Boolean = true@ @ ";
  fprintf ppf "  def compatible(that: T): Boolean = true@ ";
  List.iter (pp_vfx_intf_fn ppf) fns;
  fprintf ppf "}@]@."

let pp_vfx_cvrdt_proof ppf (name, proof, intfs) =
  let axioms = List.filter_map (function
    | Iaxiom (prop, func) -> Some (prop.id, func.id)
    | _ -> None) intfs in
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CvRDT@ @ ";
  fprintf ppf "trait %sProof[T <: CvRDT[T]] {@ @ " name;
  if proof then begin pp_vfx_is_a_cvrdt ppf ();
  fprintf ppf "@ " end;
  List.iter (fun (prop, func) ->
    pp_vfx_proof ppf (prop, func);
    fprintf ppf "@ ") axioms;
  fprintf ppf "}@]@."

let pp_vfx_cmrdt ppf (name, intfs) =
  let fns = List.filter (function Ifunc _ -> true | _ -> false) intfs in
  let has_execute = List.exists (function Ifunc (id, _, _) -> id.id = "execute" | _ -> false) fns in
  fprintf ppf "@[<v>trait %s[Op, Msg, T <: %s[Op, Msg, T]] {@ @ " name name;
  fprintf ppf "  def reachable(): Boolean = true@ @ ";
  fprintf ppf "  def compatible(x: Msg, y: Msg): Boolean = true@ @ ";
  fprintf ppf "  def compatibleS(that: T): Boolean = true@ @ ";
  fprintf ppf "  def enabledSrc(op: Op): Boolean = true@ @ ";
  fprintf ppf "  def prepare(op: Op): Msg@ @ ";
  fprintf ppf "  def enabledDown(msg: Msg): Boolean = true@ @ ";
  if has_execute then fprintf ppf "  def effect(msg: Msg): T@ @ ";
  fprintf ppf "  def tryEffect(msg: Msg): T = {@ ";
  fprintf ppf "    if (this.enabledDown(msg))@ ";
  fprintf ppf "      this.effect(msg)@ ";
  fprintf ppf "    else@ ";
  fprintf ppf "      this.asInstanceOf[T]@ ";
  fprintf ppf "  }@ @ ";
  fprintf ppf "  def equals(that: T): Boolean = {@ ";
  fprintf ppf "    this == that@ ";
  fprintf ppf "  }@ @ ";
  fprintf ppf "}@]@."

let pp_vfx_cmrdt_proof ppf (name, proof, intfs) =
  let axioms = List.filter_map (function
    | Iaxiom (prop, func) -> Some (prop.id, func.id)
    | _ -> None) intfs in
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CmRDT@ @ ";
  fprintf ppf "trait %sProof[Op, Msg, T <: CmRDT[Op, Msg, T]] {@ @ " name;
  if proof then begin pp_vfx_is_a_cmrdt ppf (); fprintf ppf "@ " end;
  List.iter (fun (prop, func) ->
    pp_vfx_proof ppf (prop, func);
    fprintf ppf "@ ") axioms;
  fprintf ppf "}@]@."


let find_payload_vfx_attr decls =
  List.fold_left (fun acc d -> match d with
    | TDtype ("payload", _, _, Some ann) -> Some ann
    | _ -> acc) None decls

let find_variant_decls decls =
  List.filter_map (function
    | TDtype (name, TTVariant (_, ctors), _, _) -> Some (name, ctors)
    | _ -> None) decls

let find_index_attr fn_name decls =
  List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = n; _ }, _, Some idx) when n = fn_name -> Some idx
    | _ -> acc) None decls

let pp_vfx_binop ppf = function
  | Badd -> pp_print_string ppf "+"
  | Bsub -> pp_print_string ppf "-"
  | Bmul -> pp_print_string ppf "*"
  | Bdiv -> pp_print_string ppf "/"
  | Beq  -> pp_print_string ppf "=="
  | Bneq -> pp_print_string ppf "!="
  | Blt  -> pp_print_string ppf "<"
  | Ble  -> pp_print_string ppf "<="
  | Bgt  -> pp_print_string ppf ">"
  | Bge  -> pp_print_string ppf ">="
  | Band -> pp_print_string ppf "&&"
  | Bor  -> pp_print_string ppf "||"

let rewrite_vfx_method_body self_param other_param class_name is_base body =
  let rec rw = function
    | TEvar v ->
        let name =
          match String.split_on_char '.' v.v_name with
          | [obj; field] when obj = self_param -> "this." ^ field
          | [obj; field] when obj = other_param -> "that." ^ field
          | [obj] when obj = self_param -> "this" ^ (if is_base then ".payload" else "")
          | [obj] when obj = other_param -> "that" ^ (if is_base then ".payload" else "")
          | _ -> v.v_name
        in
        TEvar { v with v_name = name }
    | TEcall ({ fn_name; _ } as fn, args) ->
        let fn_name' =
          if fn_name = name_init_state || fn_name = "make" then "new " ^ class_name
          else fn_name
        in
        TEcall ({ fn with fn_name = fn_name' }, List.map rw args)
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | TEnot e            -> TEnot (rw e)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw e)) fields)
    | TEmatch (e, arms)  -> TEmatch (rw e, List.map (fun (n, b) -> (n, rw b)) arms)
    | other -> other
  in
  rw body

let rec pp_vfx_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEbinop (op, l, r) ->
      fprintf ppf "(%a %a %a)" pp_vfx_texpr l pp_vfx_binop op pp_vfx_texpr r
  | TEnot e            ->
      pp_print_string ppf "!";
      pp_vfx_texpr ppf e
  | TEcall ({ fn_name; _ }, args) when fn_name = ("this.max") || fn_name = ("this.min") ->
      fprintf ppf "%s(%a)" fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) args
  | TEcall ({ fn_name; _ }, args) when String.contains fn_name '.' ->
      let parts = String.split_on_char '.' fn_name in
      let mod_name = vfx_class_name (List.nth parts 0) in
      let method_name = List.nth parts 1 in
      if method_name = "init_state" || method_name = "create" then
        fprintf ppf "new %s()" mod_name
      else if method_name = "increment" then
        fprintf ppf "%a + %a" pp_vfx_texpr (List.nth args 1) pp_vfx_texpr (List.nth args 0)
      else if method_name = "decrement" then
        fprintf ppf "%a - %a" pp_vfx_texpr (List.nth args 1) pp_vfx_texpr (List.nth args 0)
      else if method_name = "merge" then
        fprintf ppf "this.max(%a, %a)" pp_vfx_texpr (List.nth args 0) pp_vfx_texpr (List.nth args 1)
      else if method_name = "compare" then
        fprintf ppf "%a == %a" pp_vfx_texpr (List.nth args 0) pp_vfx_texpr (List.nth args 1)
      else if method_name = "get_payload" || method_name = "value" then
        begin match args with
        | [a] -> fprintf ppf "%a.value()" pp_vfx_texpr a
        | _ -> fprintf ppf "%s.value(%a)" mod_name
                 (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) args
        end
      else
        let self_is_first = method_name = "merge" || method_name = "compare" || method_name = "equals" in
        if self_is_first then
          begin match args with
          | self_arg :: rest_args ->
              fprintf ppf "%a.%s(%a)" pp_vfx_texpr self_arg method_name
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) rest_args
          | [] -> fprintf ppf "%s.%s()" mod_name method_name
          end
        else
          let rev_args = List.rev args in
          begin match rev_args with
          | self_arg :: rest_rev ->
              let normal_args = List.rev rest_rev in
              fprintf ppf "%a.%s(%a)" pp_vfx_texpr self_arg method_name
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) normal_args
          | [] -> fprintf ppf "%s.%s()" mod_name method_name
          end
  | TEcall ({ fn_name; _ }, args) when fn_name = "max" || fn_name = "min" ->
    let scala_fn = if fn_name = "max" then "Math.max" else "Math.min" in
    fprintf ppf "%s(%a)" scala_fn
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) args
  | TEcall (fn, [])    ->
      fprintf ppf "%s()" fn.fn_name
  | TEcall (fn, args)  ->
      fprintf ppf "%s(%a)" fn.fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) args
  | TErecord fields    ->
      fprintf ppf "{ %a }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ")
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_vfx_texpr e)) fields
  | TEmatch (e, arms)  ->
      fprintf ppf "%a match {@ %a@ }" pp_vfx_texpr e
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, body) ->
            fprintf ppf "  case %s() => %a" name pp_vfx_texpr body)) arms

let rewrite_vfx_vector_body self_param other_param body =
  let rec rw = function
    | TEvar v ->
        let name =
          if v.v_name = self_param then "this.payload"
          else if v.v_name = other_param then "that.payload"
          else v.v_name
        in
        TEvar { v with v_name = name }
    | TEcall ({ fn_name = ("max" | "min" as f); _ } as fn, _args) ->
        TEcall ({ fn with fn_name = f ^ "_vec" }, [])
    | TEcall (fn, args) -> TEcall (fn, List.map rw args)
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | other -> other
  in
  rw body

let rec pp_vfx_vector_expr class_name ppf = function
  | TEcall ({ fn_name = "max_vec"; _ }, []) ->
      fprintf ppf "{\n";
      fprintf ppf "    val mergedEntries = this.payload.zip(that.payload).map(this.max _)\n";
      fprintf ppf "    new %s(mergedEntries)\n" class_name;
      fprintf ppf "  }"
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEbinop (op, l, r) ->
      fprintf ppf "(%a %a %a)"
        (pp_vfx_vector_expr class_name) l pp_vfx_binop op (pp_vfx_vector_expr class_name) r
  | TEcall ({ fn_name; _ }, args) ->
      fprintf ppf "%s(%a)" fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ")
          (pp_vfx_vector_expr class_name)) args
  | other ->
      pp_vfx_texpr ppf other

let is_vector_merge_body params body =
  match body with
  | TEcall ({ fn_name = "max" | "min"; _ }, _) -> true
  | _ ->
      let param_names = List.map (fun v -> v.v_name) params in
      let rec uses_both = function
        | TEvar v -> List.mem v.v_name param_names
        | TEbinop (_, l, r) -> uses_both l || uses_both r
        | TEcall (_, args) -> List.exists uses_both args
        | _ -> false
      in
      uses_both body
let vector_element_type = function
  | Some ann ->
      let n = String.length ann in
      if n > 8 && String.sub ann 0 7 = "Vector[" && ann.[n-1] = ']'
      then String.sub ann 7 (n - 8)
      else "Int"
  | None -> "Int"

let pp_vfx_compare_body ppf (class_name, params, body, elem_type) =
  match body with
  | TEbinop (Beq, TEvar a, TEvar b)
    when List.exists (fun v -> v.v_name = a.v_name) params
      && List.exists (fun v -> v.v_name = b.v_name) params ->
      let tuple_type = Printf.sprintf "Tuple[%s, %s]" elem_type elem_type in
      fprintf ppf "def compare(that: %s): Boolean = {\n" class_name;
      fprintf ppf "    this.payload\n";
      fprintf ppf "      .zip(that.payload)\n";
      fprintf ppf "      .forall((tup: %s) => tup.fst <= tup.snd)\n" tuple_type;
      fprintf ppf "  }"
  | _ ->
      let self  = (List.nth params 0).v_name in
      let other = if List.length params > 1 then (List.nth params 1).v_name else "" in
      let body' = rewrite_vfx_method_body self other class_name true body in
      fprintf ppf "def compare(that: %s): Boolean =\n    %a"
        class_name pp_vfx_texpr body'

let pp_vfx_compute_value ppf () =
  fprintf ppf "  @recursive\n";
  fprintf ppf "  private def computeValue(sum: Int = 0, index: Int = 0): Int = {\n";
  fprintf ppf "    if (index >= 0 && index < this.payload.size) {\n";
  fprintf ppf "      val count = this.payload.get(index)\n";
  fprintf ppf "      this.computeValue(sum + count, index + 1)\n";
  fprintf ppf "    }\n";
  fprintf ppf "    else\n";
  fprintf ppf "      sum\n";
  fprintf ppf "  }\n\n";
  fprintf ppf "  def value() = this.computeValue()\n"

let pp_vfx_vector_fn ppf class_name fn_name idx_name body params =
  let self_param = match params with v :: _ -> v.v_name | [] -> "a" in
  fprintf ppf "  pre %s(%s: Int) {\n" fn_name idx_name;
  fprintf ppf "    %s >= 0 &&\n" idx_name;
  fprintf ppf "    %s < this.payload.size\n" idx_name;
  fprintf ppf "  }\n\n";
  fprintf ppf "  def %s(%s: Int) = {\n" fn_name idx_name;
  let body' = rewrite_vfx_method_body self_param "" class_name true body in
  fprintf ppf "    val count = this.payload.get(%s)\n" idx_name;
  (match body' with
   | TEbinop (op, _, rhs) ->
       fprintf ppf "    new %s(this.payload.write(%s, count %a %a))\n"
         class_name idx_name pp_vfx_binop op pp_vfx_texpr rhs
   | _ ->
       fprintf ppf "    new %s(this.payload.write(%s, %a))\n"
         class_name idx_name pp_vfx_texpr body');
  fprintf ppf "  }\n"

let rec vfx_type_of_ttp ?(elem_name = "V") = function
  | TTInt -> "Int"
  | TTBool -> "Boolean"
  | TTModuleRecord m -> vfx_class_name m
  | TTMap (k, v) -> Format.sprintf "Map[%s, %s]" (vfx_type_of_ttp ~elem_name k) (vfx_type_of_ttp ~elem_name v)
  | TTSet _  -> Printf.sprintf "Set[%s]" elem_name
  | TTAbstract _ -> elem_name
  | _ -> "Any"

let is_composite_payload fields =
  List.filter_map (fun (name, tp) ->
    match tp with
    | TTModuleRecord s when String.contains s '.' ->
        Some (name, "Int")
    | _ -> None
  ) fields

let pp_vfx_set_module ppf (mod_name, _sig_name, elem_tp, decls) =
  let class_name = vfx_class_name mod_name in
  let elem_name = match elem_tp with
    | TTAbstract n -> n
    | TTModuleRecord n -> n
    | _ -> "V"
  in
  let set_record_fields = get_set_record_fields decls in
  let is_record_set = set_record_fields <> None in
  fprintf ppf "import org.verifx.practical.crdts.CvRDT\n";
  let proof_class = "CvRDTProof" in
  fprintf ppf "import org.verifx.practical.crdts.%s\n\n" proof_class;
  if is_record_set then begin
    let fields = Option.get set_record_fields in
    let ctor_args = String.concat ", "
      (List.map (fun (n, _) ->
        Printf.sprintf "%s: Set[%s] = new Set[%s]()" n elem_name elem_name) fields) in
    fprintf ppf "class %s[%s](%s) extends CvRDT[%s[%s]] {\n"
      class_name elem_name ctor_args class_name elem_name
  end else
    fprintf ppf "class %s[%s](set: Set[%s] = new Set[%s]()) extends CvRDT[%s[%s]] {\n"
      class_name elem_name elem_name elem_name class_name elem_name;
  let rw_vfx_set_expr_with_elem =
    map_texpr (function
      | TEcall ({ fn_name = "set.empty"; _ }, _) | TEvar { v_name = "set.empty"; _ } ->
          TEvar { v_name = Printf.sprintf "new Set[%s]()" elem_name; v_tp = TTBool }
      | other -> other)
  in
  List.iter (function
    | TDtype _ -> ()
    | TDval ({ fn_name = "init_state"; _ }, _, _) -> ()
    | TDval ({ fn_name = "equals"; _ }, _, _) -> ()
    | TDval (fn, body, _) ->
        let is_binop = fn.fn_name = "merge" || fn.fn_name = "compare" in
        let self_param =
          if is_binop then (match fn.fn_params with v :: _ -> v.v_name | [] -> "a")
          else (match fn.fn_params with _ :: v :: _ -> v.v_name | v :: _ -> v.v_name | [] -> "a")
        in
        let other_param =
          if is_binop && List.length fn.fn_params >= 2
          then (List.nth fn.fn_params 1).v_name else ""
        in
        let body' = rewrite_vfx_method_body self_param other_param class_name false body in
        let body' =
          if not is_record_set then
            map_texpr (function
              | TEvar v when v.v_name = "this" -> TEvar { v with v_name = "this.set" }
              | TEvar v when v.v_name = "that" -> TEvar { v with v_name = "that.set" }
              | other -> other) body'
          else body'
        in
        let body' = rw_vfx_set_expr body' in
        let body' = rw_vfx_set_expr_with_elem body' in
        let extra_params = List.filter (fun p ->
          p.v_name <> self_param && p.v_name <> other_param) fn.fn_params in
        let pp_param ppf (v: var) =
          let tp_str = match v.v_tp with
            | TTAbstract _ -> elem_name
            | TTModuleRecord n when n = elem_name -> elem_name
            | t -> vfx_type_of_ttp ~elem_name t
          in
          fprintf ppf "%s: %s" v.v_name tp_str
        in
        let pp_body ppf b = match b with
          | TEvar v -> pp_print_string ppf v.v_name
          | TEnot e -> fprintf ppf "!%a" pp_vfx_texpr e
          | TEbinop (op, l, r) ->
              fprintf ppf "%a %a %a" pp_vfx_texpr l pp_vfx_binop op pp_vfx_texpr r
          | _ -> pp_vfx_texpr ppf b
        in
        let pp_record_body ppf b = match b with
          | TErecord fields ->
              fprintf ppf "{\n";
              List.iter (fun (n, e) ->
                fprintf ppf "    val new%s = %a\n" (String.capitalize_ascii n) pp_vfx_texpr e) fields;
              fprintf ppf "    new %s(%s)\n  }" class_name
                (String.concat ", "
                  (List.map (fun (n, _) -> "new" ^ String.capitalize_ascii n) fields))
          | other -> pp_body ppf other
        in
        if fn.fn_name = "merge" then begin
          if is_record_set then
            fprintf ppf "  def merge(that: %s[%s]) = %a\n"
              class_name elem_name pp_record_body body'
          else
            fprintf ppf "  def merge(that: %s[%s]) = new %s(%a)\n"
              class_name elem_name class_name pp_body body'
        end else if fn.fn_name = "compare" then begin
          if is_record_set then
            fprintf ppf "  def compare(that: %s[%s]) = {\n    %a\n  }\n"
              class_name elem_name pp_body body'
          else
            fprintf ppf "  def compare(that: %s[%s]) = %a\n"
              class_name elem_name pp_body body'
        end else begin
          if is_bool_ttp fn.fn_return then
            fprintf ppf "  def %s(%a) = %a\n"
              fn.fn_name
              (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_param) extra_params
              pp_body body'
          else
            if is_record_set then begin
              (* Body is a TErecord — extract field values in constructor order *)
              let fields = Option.get set_record_fields in
              let field_vals = match body' with
                | TErecord flds ->
                    List.map (fun (fname, _) ->
                      match List.assoc_opt fname flds with
                      | Some e -> e
                      | None -> TEvar { v_name = "this." ^ fname; v_tp = TTBool }
                    ) fields
                | other -> [other]
              in
              fprintf ppf "  def %s(%a) = new %s(%a)\n"
                fn.fn_name
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_param) extra_params
                class_name
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_vfx_texpr) field_vals
            end else
              fprintf ppf "  def %s(%a) = new %s(%a)\n"
                fn.fn_name
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_param) extra_params
                class_name pp_body body'
        end
  ) decls;
  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends %s[%s]\n" class_name proof_class class_name

let pp_vfx_composite_invariant ppf inv_body self_param class_name =
  match inv_body with
  | TEbinop (Beq, TEvar v, rhs) when String.length v.v_name > 8 && String.sub v.v_name (String.length v.v_name - 8) 8 = ".payload" ->
      let rhs' = rewrite_vfx_method_body self_param "" class_name false rhs in
      let rec rewrite_value_calls = function
        | TEvar vv when String.contains vv.v_name '.' ->
            TEvar vv
        | TEbinop (op, l, r) -> TEbinop (op, rewrite_value_calls l, rewrite_value_calls r)
        | other -> other
      in
      let rhs'' = rewrite_value_calls rhs' in
      fprintf ppf "  def value() = {\n    %a\n  }\n\n" pp_vfx_texpr rhs''
  | _ -> ()

let merge_uses_minmax body =
  match body with
  | TEcall ({ fn_name = ("max" | "min") as op; _ }, [_; _]) -> Some op
  | _ -> None

let rec rewrite_minmax_to_method = function
  | TEcall ({ fn_name = ("max" | "min") as op; _ } as fn, args) ->
      TEcall ({ fn with fn_name = "this." ^ op }, List.map rewrite_minmax_to_method args)
  | TEbinop (op, l, r) -> TEbinop (op, rewrite_minmax_to_method l, rewrite_minmax_to_method r)
  | other -> other

let pp_vfx_method is_base class_name ppf (fn: fn) body =
  let is_binop = fn.fn_name = "merge" || fn.fn_name = "compare" || fn.fn_name = "equals" in
  let self = if is_binop then (List.nth fn.fn_params 0).v_name
             else if List.length fn.fn_params >= 2 then (List.nth fn.fn_params 1).v_name else "a" in
  let other = if is_binop && List.length fn.fn_params >= 2 then (List.nth fn.fn_params 1).v_name else "" in
  let body' = rewrite_vfx_method_body self other class_name is_base body in
  let body' = if is_base && fn.fn_name = "merge" then rewrite_minmax_to_method body' else body' in

  let pp_top_level ppf = function
    | TEbinop (op, l, r) -> fprintf ppf "%a %a %a" pp_vfx_texpr l pp_vfx_binop op pp_vfx_texpr r
    | other -> pp_vfx_texpr ppf other
  in

  let wrap_expr ppf b =
    if is_base && fn.fn_name <> "value" && fn.fn_name <> "get_payload" && fn.fn_name <> "compare" then
      fprintf ppf "new %s(%a)" class_name pp_top_level b
    else
      pp_top_level ppf b
  in

  if fn.fn_name = "compare" then
    fprintf ppf "  def compare(that: %s): Boolean = {\n    %a\n  }\n\n" class_name pp_top_level body'
  else if fn.fn_name = "merge" then
    fprintf ppf "  def merge(that: %s) = {\n    %a\n  }\n\n" class_name wrap_expr body'
  else
    let args = List.filter (fun p -> p.v_name <> self) fn.fn_params in
    let pp_arg ppf (v: var) = fprintf ppf "%s: %s" v.v_name (vfx_type_of_ttp v.v_tp) in
    fprintf ppf "  def %s(%a) = {\n    %a\n  }\n\n" fn.fn_name
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_arg) args
      wrap_expr body'

let pp_vfx_cvrdt_module ppf (mod_name, sig_name, decls) =
  let class_name = vfx_class_name mod_name in
  let payload_decl = List.find_opt (function TDtype ("payload", _, _, _) -> true | _ -> false) decls in

  let is_composite, comp_fields, inv_opt =
    match payload_decl with
    | Some (TDtype (_, TTRecord fields, inv, _)) ->
        let cf = is_composite_payload fields in
        if cf <> [] then (true, cf, inv) else (false, [], inv)
    | _ -> (false, [], None)
  in

  let payload_ann = find_payload_vfx_attr decls in
  let is_vector = match payload_ann with Some ann when String.length ann > 0 -> true | _ -> false in

  fprintf ppf "import org.verifx.practical.crdts.CvRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.CvRDTProof\n\n";

  if is_composite then begin
    let ctor_args = String.concat ", " (List.map (fun (n, t) -> n ^ ": " ^ t) comp_fields) in
    fprintf ppf "class %s(%s) extends CvRDT[%s] {\n\n" class_name ctor_args class_name;
    (match inv_opt with
     | Some (_, inv_body) -> pp_vfx_composite_invariant ppf inv_body "a" class_name
     | None -> ());
    List.iter (function
      | TDval (fn, body, _) when fn.fn_name <> "init_state" && fn.fn_name <> "make" && fn.fn_name <> "equals" ->
          if fn.fn_name = "merge" then begin
            fprintf ppf "  private def max(a: Int, b: Int) = {\n    if (a >= b) a else b\n  }\n\n"
          end;
          pp_vfx_method false class_name ppf fn body
      | _ -> ()) decls;
    fprintf ppf "}\n\n"
  end else if is_vector then begin
    let vector_type = match payload_ann with Some ann -> ann | None -> "Vector[Int]" in
    let elem_type = vector_element_type payload_ann in
    let tuple_type = Printf.sprintf "Tuple[%s, %s]" elem_type elem_type in
    fprintf ppf "class %s(payload: %s) extends CvRDT[%s] {\n\n" class_name vector_type class_name;
    List.iter (function
      | TDval (fn, body, Some (idx_name, _)) ->
          pp_vfx_vector_fn ppf class_name fn.fn_name idx_name body fn.fn_params;
          fprintf ppf "\n"
      | _ -> ()) decls;
    pp_vfx_compute_value ppf ();
    fprintf ppf "\n  private def max(t: %s) = if (t.fst >= t.snd) t.fst else t.snd\n\n" tuple_type;
    (match List.find_opt (function TDval ({ fn_name = "merge"; _ }, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _)) ->
         let self  = match fn.fn_params with v :: _ -> v.v_name | [] -> "a" in
         let other = match fn.fn_params with _ :: v :: _ -> v.v_name | _ -> "b" in
         let body' = rewrite_vfx_vector_body self other body in
         fprintf ppf "  def merge(that: %s): %s = %a\n\n" class_name class_name (pp_vfx_vector_expr class_name) body'
     | _ -> ());
    (match List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _)) ->
         fprintf ppf "  ";
         pp_vfx_compare_body ppf (class_name, fn.fn_params, body, elem_type);
         fprintf ppf "\n"
     | _ -> ());
    fprintf ppf "}\n\n"
  end else begin
    let base_type = match payload_decl with
      | Some (TDtype (_, tp, _, _)) -> vfx_type_of_ttp tp
      | _ -> "Int"
    in
    let merge_decl = List.find_opt (function TDval ({ fn_name = "merge"; _ }, _, _) -> true | _ -> false) decls in
    let minmax_op = match merge_decl with
      | Some (TDval (_, body, _)) -> merge_uses_minmax body
      | _ -> None
    in
    fprintf ppf "class %s(payload: %s) extends CvRDT[%s] {\n\n" class_name base_type class_name;

    List.iter (function
      | TDval (fn, body, _)
        when fn.fn_name <> "init_state" && fn.fn_name <> "equals"
          && fn.fn_name <> "merge" && fn.fn_name <> "compare" ->
          pp_vfx_method true class_name ppf fn body
      | _ -> ()) decls;

    let has_value = List.exists (function
      | TDval ({ fn_name = "value"; _ }, _, _) -> true | _ -> false) decls in
    if not has_value then
      fprintf ppf "  def value(): %s = {\n    this.payload\n  }\n\n" base_type;

    (match minmax_op with
     | Some op ->
         let cmp = if op = "max" then ">=" else "<=" in
         fprintf ppf "  private def %s(a: %s, b: %s): %s = {\n" op base_type base_type base_type;
         fprintf ppf "    if (a %s b) a else b\n" cmp;
         fprintf ppf "  }\n\n"
     | None -> ());

    (match merge_decl with
     | Some (TDval (fn, body, _)) -> pp_vfx_method true class_name ppf fn body
     | Some (TDtype _) | None -> ());
    (match List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _)) -> pp_vfx_method true class_name ppf fn body
     | Some (TDtype _) | None -> ());

    fprintf ppf "}\n\n"
  end;

  fprintf ppf "object %s extends CvRDTProof[%s]\n" class_name class_name;
  ignore sig_name

let lowercase_first s =
  if String.length s = 0 then s
  else String.make 1 (Char.lowercase_ascii s.[0]) ^ String.sub s 1 (String.length s - 1)

let pp_vfx_cmrdt_helper ppf class_name payload_field state_param (ctor, body) =
  let helper_name = lowercase_first ctor in
  let body' = rewrite_vfx_method_body state_param "" class_name false body in
  fprintf ppf "  def %s() = new %s(this.%s %a)\n"
    helper_name class_name payload_field
    (fun ppf e -> match e with
       | TEbinop (op, _, rhs) ->
           fprintf ppf "%a %a" pp_vfx_binop op pp_vfx_texpr rhs
       | _ ->
           pp_vfx_texpr ppf e) body'

let pp_vfx_effect_arm ppf (ctor, _body) =
  let helper_name = lowercase_first ctor in
  fprintf ppf "    case %s() => this.%s()\n" ctor helper_name

let pp_vfx_cmrdt_module ppf (mod_name, sig_name, decls) =
  let class_name = vfx_class_name mod_name in
  let variants = find_variant_decls decls in
  let (op_type_name, op_ctors) = match variants with
    | (name, ctors) :: _ -> (name, ctors)
    | [] -> ("Operation", [])
  in
  let execute_info = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "execute"; fn_params; _ }, body, _) ->
        let state_param = match fn_params with
          | _ :: v :: _ -> v.v_name
          | v :: _      -> v.v_name
          | []          -> "state"
        in
        Some (state_param, body)
    | _ -> acc) None decls
  in
  let payload_field = match List.find_opt (function
    | TDtype ("payload", TTRecord ((_, _) :: _), _, _) -> true
    | _ -> false) decls with
    | Some (TDtype ("payload", TTRecord ((f, _) :: _), _, _)) -> f
    | _ -> "ctr"
  in
  let ctor_arg_type = match List.find_opt
    (function TDtype ("payload", _, _, _) -> true | _ -> false) decls with
    | Some (TDtype (_, tp, _, _)) -> vfx_type_of_ttp tp
    | _ -> "Int"
  in
  let default_value = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "init_state"; _ }, TErecord fields, _) ->
        (match List.assoc_opt payload_field fields with
         | Some (TEcst (Cint n)) -> Some (Int64.to_string n)
         | Some (TEcst (Cbool b)) -> Some (string_of_bool b)
         | _ -> acc)
    | TDval ({ fn_name = "init_state"; _ }, TEcst (Cint n), _) ->
        Some (Int64.to_string n)
    | _ -> acc) None decls
  in
  fprintf ppf "import org.verifx.practical.crdts.CmRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.CmRDTProof\n\n";
  if op_ctors <> [] then begin
    fprintf ppf "object %s {\n" op_type_name;
    fprintf ppf "  enum %s {\n" op_type_name;
    fprintf ppf "    %s\n"
      (String.concat " | " (List.map (fun c -> c ^ "()") op_ctors));
    fprintf ppf "  }\n";
    fprintf ppf "}\n\n"
  end;
  (match default_value with
   | Some v ->
       fprintf ppf "class %s(%s: %s = %s) extends CmRDT[%s, %s, %s] {\n"
         class_name payload_field ctor_arg_type v op_type_name op_type_name class_name
   | None ->
       fprintf ppf "class %s(%s: %s) extends CmRDT[%s, %s, %s] {\n"
         class_name payload_field ctor_arg_type op_type_name op_type_name class_name);
  (match execute_info with
   | Some (state_param, TEmatch (_, arms)) ->
       List.iter (pp_vfx_cmrdt_helper ppf class_name payload_field state_param) arms;
       fprintf ppf "\n"
   | _ -> fprintf ppf "\n");
  fprintf ppf "  def prepare(op: %s) = op\n\n" op_type_name;
  fprintf ppf "  def effect(op: %s) = op match {\n" op_type_name;
  (match execute_info with
   | Some (_, TEmatch (_, arms)) ->
       List.iter (pp_vfx_effect_arm ppf) arms
   | _ ->
       fprintf ppf "    (* no execute body found *)\n");
  fprintf ppf "  }\n";
  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends CmRDTProof[%s, %s, %s]\n"
    class_name op_type_name op_type_name class_name;
  ignore sig_name

let is_cvrdt_sig sig_name = sig_name = "CvRDT"
let is_cmrdt_sig sig_name = sig_name = "CmRDT"

let pp_vfx_module ppf (mod_name, sig_name, _intfs, decls) =
  if is_cvrdt_sig sig_name then begin
    match get_set_elem_type decls with
    | Some elem_tp -> pp_vfx_set_module ppf (mod_name, sig_name, elem_tp, decls)
    | None         -> pp_vfx_cvrdt_module ppf (mod_name, sig_name, decls)
  end else if is_cmrdt_sig sig_name then begin
    pp_vfx_cmrdt_module ppf (mod_name, sig_name, decls)
  end

let vfx_module_files_of_tfile tfile =
  let exercises_path = "verifx/src/main/verifx/org/verifx/practical/exercises/" in
  
  List.filter_map (function
    | TDefModule (mod_name, sig_name, intfs, decls) ->
        let class_name = vfx_class_name mod_name in
        let should_emit = is_cvrdt_sig sig_name || is_cmrdt_sig sig_name in
        if should_emit then
          let path = exercises_path ^ class_name ^ ".vfx" in
          Some (path, fun fmt ->
            pp_vfx_module fmt (mod_name, sig_name, intfs, decls))
        else
          None
    | TDefInterface _ -> None) tfile

let vfx_files_of_tfile tfile =
  let crdts_path = "verifx/src/main/verifx/org/verifx/practical/crdts/" in
  
  let intf_files = List.filter_map (function
    | TDefInterface (name, proof, intfs) ->
        if is_cvrdt_interface intfs then
          Some [
            (crdts_path ^ name ^ ".vfx",      fun fmt -> pp_vfx_cvrdt fmt (name, intfs));
            (crdts_path ^ name ^ "Proof.vfx", fun fmt -> pp_vfx_cvrdt_proof fmt (name, proof, intfs));
          ]
        else
          Some [
            (crdts_path ^ name ^ ".vfx",      fun fmt -> pp_vfx_cmrdt fmt (name, intfs));
            (crdts_path ^ name ^ "Proof.vfx", fun fmt -> pp_vfx_cmrdt_proof fmt (name, proof, intfs));
          ]
    | TDefModule _ -> None) tfile
  |> List.flatten
  in
  let module_files = vfx_module_files_of_tfile tfile in
  intf_files @ module_files
