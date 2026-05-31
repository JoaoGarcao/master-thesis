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

let strip_crdt_suffix name =
  match String.split_on_char '_' name with
  | base :: _ -> base
  | []        -> name

let uppercase_initials name =
  let buf = Buffer.create 4 in
  String.iter (fun c -> if c >= 'A' && c <= 'Z' then Buffer.add_char buf c) name;
  Buffer.contents buf

let derive_names mod_name =
  let base     = strip_crdt_suffix mod_name in
  let initials = uppercase_initials base in
  (initials ^ "Auxiliary", base, initials ^ "Aux")

let module_registry : (string, string * string) Hashtbl.t = Hashtbl.create 8

let aux_alias_of_module mod_name =
  match Hashtbl.find_opt module_registry mod_name with
  | Some (_, alias) -> Some alias
  | None -> None

let rewrite_module_refs expr =
  let rewrite_fn_name name =
    match String.split_on_char '.' name with
    | [mod_name; fn_name] ->
        begin match aux_alias_of_module mod_name with
        | Some alias -> alias ^ "." ^ fn_name
        | None -> name
        end
    | _ -> name
  in
  let rewrite_var_name name =
    match String.split_on_char '.' name with
    | [mod_name; fn_name] ->
        begin match aux_alias_of_module mod_name with
        | Some alias -> alias ^ "." ^ fn_name
        | None -> name
        end
    | _ -> name
  in
  let rec rw = function
    | TEvar v -> TEvar { v with v_name = rewrite_var_name v.v_name }
    | TEcall (fn, args) ->
        TEcall ({ fn with fn_name = rewrite_fn_name fn.fn_name }, List.map rw args)
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | TErecord fields -> TErecord (List.map (fun (n, e) -> (n, rw e)) fields)
    | TEmatch (e, arms) -> TEmatch (rw e, List.map (fun (n, b) -> (n, rw b)) arms)
    | other -> other
  in
  rw expr

let uses_int_int = ref false
let uses_min_max = ref false

let reset_uses () =
  uses_int_int := false;
  uses_min_max := false

let rec scan_ttp = function
  | TTInt | TTBool            -> uses_int_int := true
  | TTMap (k, v)              -> scan_ttp k; scan_ttp v
  | TTRecord fields           -> List.iter (fun (_, t) -> scan_ttp t) fields
  | _                         -> ()

let rec scan_texpr = function
  | TEcall (fn, args) ->
      if fn.fn_name = "max" || fn.fn_name = "min" then begin
        uses_int_int := true;
        uses_min_max := true
      end;
      List.iter scan_texpr args
  | TEbinop (_, l, r)  -> scan_texpr l; scan_texpr r
  | TErecord fields    -> List.iter (fun (_, e) -> scan_texpr e) fields
  | TEmatch (e, arms)  -> scan_texpr e; List.iter (fun (_, b) -> scan_texpr b) arms
  | _                  -> ()

let scan_tmodl = function
  | TDtype (_, tp, _)  -> scan_ttp tp
  | TDval (fn, body)   ->
      List.iter (fun v -> scan_ttp v.v_tp) fn.fn_params;
      scan_ttp fn.fn_return;
      scan_texpr body

let rec pp_w3_ttp ppf = function
  | TTInt              -> pp_print_string ppf "int"
  | TTBool             -> pp_print_string ppf "bool"
  | TTMap (k, v)       -> fprintf ppf "map %a %a" pp_w3_ttp k pp_w3_ttp v
  | TTRecord fields    ->
      fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, tp) -> fprintf ppf "%s: %a;" name pp_w3_ttp tp))
        fields
  | TTInvariant names  -> pp_print_string ppf (String.concat " " names)
  | TTModuleRecord m   -> pp_print_string ppf m
  | TTVariant (_, _)   -> pp_print_string ppf "(* variant *)"

let rec pp_w3_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEbinop (op, l, r) ->
      fprintf ppf "@[<hv 1>%a@ %a@ %a@]" pp_w3_texpr l pp_w3_binop op pp_w3_texpr r
  | TEcall (fn, [])   ->
      fprintf ppf "%s ()" fn.fn_name
  | TEcall (fn, args)  ->
      fprintf ppf "@[<h>%s@ %a@]"
        fn.fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_w3_texpr_atom) args
  | TErecord fields    ->
      fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ";@ ")
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_w3_texpr e))
        fields
  | TEmatch (e, arms)  ->
      fprintf ppf "@[<v>match %a with@ %a@ end@]"
        pp_w3_texpr e
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, body) ->
            match body with
            | TErecord _ ->
                fprintf ppf "@[<hv 2>| %s ->@ %a@]" name pp_w3_texpr body
            | _ ->
                fprintf ppf "@[<hv 2>| %s ->@ { payload = %a }@]" name pp_w3_texpr body))
        arms

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
    (fun ppf (vs, tp) ->
      fprintf ppf "(%a: %a)"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ")
          (fun ppf v -> pp_print_string ppf v.v_name)) vs
        pp_w3_ttp tp)
    ppf (group params)

let pp_w3_uses ppf () =
  if !uses_int_int && !uses_min_max then
    fprintf ppf "use int.Int, int.MinMax@ @ "
  else if !uses_int_int then
    fprintf ppf "use int.Int@ @ "

let is_bool_ttp = function TTBool -> true | _ -> false

let interface_fn_names intfs =
  List.filter_map (function
    | Ifunc (id, _, _) -> Some id.id
    | Itype _ | Iaxiom _ -> None) intfs

let is_two_module_interface intfs =
  let fns = interface_fn_names intfs in
  List.mem "merge" fns && List.mem "compare" fns

let payload_param_names fn =
  List.filter_map (fun v ->
    if v.v_tp = TTModuleRecord "payload" then Some v.v_name
    else None) fn.fn_params

let rewrite_texpr_for_aux payload_vars body =
  let rec rw = function
    | TEvar v when List.mem v.v_name payload_vars ->
        TEvar { v with v_name = v.v_name ^ ".payload" }
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | TEcall (fn, args)  -> TEcall (fn, List.map rw args)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw e)) fields)
    | TEmatch (e, arms)  -> TEmatch (rw e, List.map (fun (n, b) -> (n, rw b)) arms)
    | other              -> other
  in
  rw body

let pp_w3_aux_decl ppf = function
  | TDtype (name, TTVariant (_, ctors), _) ->
      fprintf ppf "@[type %s =@ %a@]"
        name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " | ")
          pp_print_string) ctors

  | TDtype ("payload", tp, _) ->
      fprintf ppf "@[type payload = %a@]" pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = { payload: %a; }@]" pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let function get_payload (a: t) : payload@ = a.payload@]"

  | TDtype (name, tp, _) ->
      fprintf ppf "@[type %s = %a@]" name pp_w3_ttp tp

  | TDval ({ fn_name = "init_state"; _ }, body) ->
      fprintf ppf "@[<v 2>let ghost function create () : t@ = { payload = %a }@]"
        pp_w3_texpr body

  | TDval (fn, body) ->
      let rewrite_param v =
        if v.v_tp = TTModuleRecord "payload" then { v with v_tp = TTModuleRecord "t" }
        else v
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let pvars = payload_param_names fn in
      let ret =
        if fn.fn_return = TTModuleRecord "payload" then TTModuleRecord "t"
        else fn.fn_return
      in
      let rewritten = rewrite_texpr_for_aux pvars body in
      let pp_aux_match_arm ppf (name, arm_body) =
        match arm_body with
        | TErecord _ ->
            fprintf ppf "@[<hv 2>| %s ->@ %a@]" name pp_w3_texpr arm_body
        | _ ->
            fprintf ppf "@[<hv 2>| %s ->@ { payload = %a }@]" name pp_w3_texpr arm_body
      in
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[<v 2>predicate %s %a@ = %a@]"
          fn.fn_name pp_w3_tparams tparams pp_w3_texpr rewritten
      else begin
        match rewritten with
        | TEmatch (e, arms) ->
            fprintf ppf "@[<v 2>function %s %a : %a@ = @[<v>match %a with@ %a@ end@]@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret
              pp_w3_texpr e
              (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") pp_aux_match_arm) arms
        | _ ->
            fprintf ppf "@[<v 2>let function %s %a : %a@ = { payload = %a }@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret pp_w3_texpr rewritten
      end

let pp_w3_auxiliary ppf aux_mod intfs decls =
  reset_uses ();
  List.iter scan_tmodl decls;
  let aux_only_exclude = List.filter_map (function
    | Ifunc (id, _, _) when id.id = "equals" -> Some id.id
    | _ -> None) intfs in
  let aux_decls = List.filter (function
    | TDval (fn, _) -> not (List.mem fn.fn_name aux_only_exclude)
    | _ -> true) decls in
  let variant_decls = List.filter (function TDtype (_, TTVariant _, _) -> true | _ -> false) aux_decls in
  let other_decls = List.filter (function TDtype (_, TTVariant _, _) -> false | _ -> true) aux_decls in
  let ordered = variant_decls @ other_decls in
  fprintf ppf "@[<v 2>module %s@ @ %a%a@]@ @ end@ "
    aux_mod
    pp_w3_uses ()
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_aux_decl) ordered

let pp_w3_main_decl ppf (aux_alias, _payload_tp, tmodl) =
  match tmodl with
  | TDtype ("payload", _, _) ->
      fprintf ppf "@[type payload = %s.payload@]" aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = %s.t@]" aux_alias

  | TDtype (name, _, _) ->
      fprintf ppf "@[type %s = %s.%s@]" name aux_alias name

  | TDval ({ fn_name = "init_state"; _ }, _) ->
      fprintf ppf "@[<v 2>let function get_payload (a: t) : %a@ = %s.get_payload a@]"
        pp_w3_ttp _payload_tp aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let ghost function create () : t@ = %s.create ()@]" aux_alias

  | TDval ({ fn_name = "equals"; _ }, _) ->
      fprintf ppf "@[<v>predicate equals (a b: t)@ = compare a b /\\ compare b a@]"

  | TDval (fn, _) ->
      let rewrite_param v =
        if v.v_tp = TTModuleRecord "payload" then { v with v_tp = TTModuleRecord "t" }
        else v
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let param_names ppf ps =
        pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
          (fun ppf v -> pp_print_string ppf v.v_name) ppf ps
      in
      let ret =
        if fn.fn_return = TTModuleRecord "payload" then TTModuleRecord "t"
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
    | TDtype ("payload", tp, _) -> tp
    | _ -> acc) TTInt decls in
  let intf_fns = interface_fn_names intfs in
  let interface_decls = List.filter (function
    | TDtype _ -> true
    | TDval (fn, _) -> List.mem fn.fn_name intf_fns) decls in
  fprintf ppf "@[<v 2>module %s : %s@ @ %ause %s as %s@ @ %a@]@ @ end@ "
    main_mod sig_name
    pp_w3_uses ()
    aux_mod aux_alias
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
      (fun ppf d -> pp_w3_main_decl ppf (aux_alias, payload_tp, d))) interface_decls
let get_composite_source decls =
  List.fold_left (fun acc d -> match d, acc with
    | TDtype ("payload", TTRecord fields, _), None ->
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

let rewrite_composite_field_tp alias = function
  | TTModuleRecord s when String.contains s '.' ->
      let parts = String.split_on_char '.' s in
      begin match parts with
      | [_mod; _field] -> TTModuleRecord (alias ^ ".t")
      | _ -> TTModuleRecord s
      end
  | other -> other

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
      (fun ppf (prop, func) -> pp_w3_axiom ppf (prop, func))
      ppf axioms
  end

let resolve_intf_tp = function
  | Tcst { id = "boolean"; _ } -> TTBool
  | Tcst { id = "payload"; _ } -> TTModuleRecord "t"
  | Tcst { id = other; _ }     -> TTModuleRecord other
  | _                          -> TTModuleRecord "t"

let pp_w3_intf_decl ppf = function
  | Itype id ->
      fprintf ppf "@[type %s@]" id.id
  | Ifunc (id, [], _tp) ->
      if id.id = "init_state" then
        fprintf ppf "@[val ghost function create () : t@]"
      else
        fprintf ppf "@[val function %s (t: t) : payload@]" id.id
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
    | Itype id -> id.id = "payload"
    | _ -> false) intfs in
  let other_types = List.filter (function
    | Itype id -> id.id <> "payload"
    | _ -> false) intfs in
  let funcs = List.filter (function
    | Ifunc (id, _, _) -> id.id <> "equals" && id.id <> "init_state"
    | _ -> false) intfs in
  fprintf ppf "@[<v 2>module %s@ @ %a@ @ @[type t@]@ @ %a@[val ghost function create () : t@]@ @ @[val function get_payload (a: t) : payload@]@ @ %a@ @ @[<v>predicate equals (a b: t)@ = compare a b /\\ compare b a@]%a@]@ @ end@ "
    name
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_intf_decl) payload_types
    (fun ppf types -> if types <> [] then
      fprintf ppf "%a@ @ "
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_intf_decl) types
    else ()) other_types
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_intf_decl) funcs
    pp_w3_axioms intfs
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

  let payload_fields = List.fold_left (fun acc d -> match d with
    | TDtype ("payload", TTRecord fields, _) -> fields
    | _ -> acc) [] decls in

  let inv_opt = List.fold_left (fun acc d -> match d with
    | TDtype ("payload", _, inv) -> inv
    | _ -> acc) None decls in

  let init_body = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "init_state"; _ }, body) -> Some body
    | _ -> acc) None decls in

  let intf_fns = interface_fn_names intfs in

  let translate_fn_name fn_name =
    match String.split_on_char '.' fn_name with
    | [m; f] when Hashtbl.mem module_registry m ->
        let (_, alias) = Hashtbl.find module_registry m in
        let f' = if f = "init_state" then "create" else f in
        alias ^ "." ^ f'
    | _ ->
        if fn_name = "init_state" then "create" else fn_name
  in
  let rec rw_expr = function
    | TEvar v ->
        let n = match String.split_on_char '.' v.v_name with
          | [m; f] when Hashtbl.mem module_registry m ->
              let (_, alias) = Hashtbl.find module_registry m in alias ^ "." ^ f
          | _ -> v.v_name in
        TEvar { v with v_name = n }
    | TEcall (fn, args) ->
        let fn_name = translate_fn_name fn.fn_name in
        TEcall ({ fn with fn_name }, List.map rw_expr args)
    | TEbinop (op, l, r) -> TEbinop (op, rw_expr l, rw_expr r)
    | TErecord fields ->
        TErecord (List.map (fun (n, e) ->
          let n' = if n = "payload" then payload_fn else n in
          (n', rw_expr e)) fields)
    | TEmatch (e, arms) -> TEmatch (rw_expr e, List.map (fun (n, b) -> (n, rw_expr b)) arms)
    | other -> other
  in

  let rec rw_inv_expr = function
    | TEvar v ->
        let n = v.v_name in
        let n = match String.split_on_char '.' n with
          | [_var; "payload"] -> payload_fn
          | [_var; field] -> field
          | _ -> n
        in
        TEvar { v with v_name = n }
    | TEcall (fn, args) ->
        let fn_name = match String.split_on_char '.' fn.fn_name with
          | [m; f] when Hashtbl.mem module_registry m ->
              let (_, alias) = Hashtbl.find module_registry m in alias ^ "." ^ f
          | _ -> fn.fn_name in
        TEcall ({ fn with fn_name }, List.map rw_inv_expr args)
    | TEbinop (op, l, r) -> TEbinop (op, rw_inv_expr l, rw_inv_expr r)
    | other -> other
  in

  let rw_inv_field_access expr =
    let ext_fields = List.filter_map (fun (name, tp) ->
      match tp with
      | TTModuleRecord s when String.contains s '.' -> Some name
      | _ -> None) payload_fields in
    let rec rw = function
      | TEvar v when List.mem v.v_name ext_fields ->
          let get_fn = { fn_name = aux_alias ^ ".get_payload";
                        fn_params = []; fn_return = TTInt } in
          TEcall (get_fn, [TEvar v])
      | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
      | TEcall (fn, args) -> TEcall (fn, List.map rw args)
      | other -> other
    in
    rw expr
  in

  let rw_init_field (name, e) =
    let fname = if name = "payload" then payload_fn else name in
    (fname, rw_expr e)
  in

  fprintf ppf "@[<v 2>module %s : %s@ @ use int.Int@ use %s as %s@ @ "
    main_mod sig_name aux_mod aux_alias;

  fprintf ppf "@[type payload = int@]@ @ ";

  fprintf ppf "type t = { %a }@ "
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
      (fun ppf (name, tp) ->
        let tp' = match tp with
          | TTModuleRecord s when String.contains s '.' ->
              TTModuleRecord (aux_alias ^ ".t")
          | other -> other
        in
        let fname = if name = "payload" then payload_fn else name in
        let tp'' = if name = "payload" then TTModuleRecord "payload" else tp' in
        fprintf ppf "%s: %a" fname pp_w3_ttp tp''))
    payload_fields;

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

  fprintf ppf "@[<v 2>let function get_payload (a: t) : payload@ = a.%s@]@ @ " payload_fn;

  begin match init_body with
  | Some (TErecord fields) ->
      fprintf ppf "@[<v 2>let ghost function create () : t@ = { %a }@]@ @ "
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ")
          (fun ppf f -> let (n, e) = rw_init_field f in
            fprintf ppf "%s = %a" n pp_w3_texpr e))
        fields
  | _ -> ()
  end;

  let make_decl = List.find_opt (function TDval ({ fn_name = "make"; _ }, _) -> true | _ -> false) decls in
  begin match make_decl with
  | Some (TDval (fn, body)) ->
      let rewrite_param v =
        match v.v_tp with
        | TTModuleRecord s when String.contains s '.' ->
            { v with v_tp = TTModuleRecord (aux_alias ^ ".t") }
        | other -> { v with v_tp = other }
      in
      let tparams = List.map rewrite_param fn.fn_params in
      let body' = rw_expr body in
      fprintf ppf "@[<v 2>let function make %a : t@ = %a@]@ @ "
        pp_w3_tparams tparams pp_w3_texpr body'
  | _ -> ()
  end;

  let other_decls = List.filter (function
    | TDtype _ -> false
    | TDval ({ fn_name; _ }, _) ->
        fn_name <> "init_state" && fn_name <> "make") decls in

  let pp_composite_decl ppf = function
    | TDval ({ fn_name = "equals"; _ }, _) ->
        fprintf ppf "@[<v>predicate equals (a b: t)@ = compare a b /\\ compare b a@]"
    | TDval (fn, body) ->
        let rewrite_param v =
          match v.v_tp with
          | TTModuleRecord "payload" -> { v with v_tp = TTModuleRecord "t" }
          | other -> { v with v_tp = other }
        in
        let tparams = List.map rewrite_param fn.fn_params in
        let body' = rw_expr body in
        if is_bool_ttp fn.fn_return then
          fprintf ppf "@[<v 2>predicate %s %a@ = %a@]"
            fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
        else begin
          match body' with
          | TErecord fields when not (List.exists (fun (n, _) -> n = payload_fn) fields) ->
              let make_args = List.filter_map (fun (n, e) ->
                if n <> payload_fn then Some e else None) fields in
              fprintf ppf "@[<v 2>function %s %a : t@ = make %a@]"
                fn.fn_name pp_w3_tparams tparams
                (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_w3_texpr_atom) make_args
          | _ ->
              let is_match = match body' with TEmatch _ -> true | _ -> false in
              if is_match then
                fprintf ppf "@[<v 2>function %s %a : t@ = %a@]"
                  fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
              else
                fprintf ppf "@[<v 2>let function %s %a : t@ = %a@]"
                  fn.fn_name pp_w3_tparams tparams pp_w3_texpr body'
        end
    | _ -> ()
  in

  let intf_decls = List.filter (function
    | TDval (fn, _) -> List.mem fn.fn_name intf_fns | _ -> false) other_decls in
  let extra_decls = List.filter (function
    | TDval (fn, _) -> not (List.mem fn.fn_name intf_fns) | _ -> false) other_decls in
  let ordered = extra_decls @ intf_decls in

  pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
    pp_composite_decl ppf ordered;

  fprintf ppf "@]@ @ end@ "


let pp_w3_tdef ppf = function
  | TDefInterface (name, intfs) ->
      pp_w3_interface ppf (name, intfs)
  | TDefModule (name, sig_name, intfs, decls) ->
      let (aux_mod, main_mod, aux_alias) = derive_names name in
      Hashtbl.replace module_registry name (aux_mod, aux_alias);
      let is_composite = get_composite_source decls <> None in
      if is_composite then begin
        pp_w3_composite ppf (main_mod, sig_name, intfs, decls)
      end else if is_two_module_interface intfs then begin
        pp_w3_auxiliary ppf aux_mod intfs decls;
        fprintf ppf "@ @ ";
        pp_w3_main ppf (main_mod, sig_name, aux_mod, aux_alias, intfs, decls)
      end else begin
        reset_uses ();
        List.iter scan_tmodl decls;
        let variant_decls = List.filter (function TDtype (_, TTVariant _, _) -> true | _ -> false) decls in
        let other_decls = List.filter (function TDtype (_, TTVariant _, _) -> false | _ -> true) decls in
        let ordered = variant_decls @ other_decls in
        fprintf ppf "@[<v 2>module %s : %s@ @ %a%a@]@ @ end@ "
          main_mod sig_name
          pp_w3_uses ()
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ")
            (fun ppf d -> match d with
              | TDval ({ fn_name = "equals"; _ }, _) ->
                  fprintf ppf "@[<v>predicate equals (a b: t)@ = compare a b /\\ compare b a@]"
              | _ -> pp_w3_aux_decl ppf d)) ordered
      end

let pp_w3_tfile ppf defs =
  fprintf ppf "@[<v>%a@]@."
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") pp_w3_tdef) defs

let print_w3_tfile tfile = pp_w3_tfile std_formatter tfile
let write_w3_tfile fmt tfile = pp_w3_tfile fmt tfile