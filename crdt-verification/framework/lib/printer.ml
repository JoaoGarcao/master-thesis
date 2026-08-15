open Format
open Ast

let pp_sep_comma ppf () = fprintf ppf ", "
let pp_sep_break ppf () = fprintf ppf "@ "
let pp_sep_blank ppf () = fprintf ppf "@ @ "
let pp_sep_space ppf () = fprintf ppf " "
let pp_sep_semi ppf () = fprintf ppf "; "
let pp_sep_bar ppf () = fprintf ppf " | "

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
  | Biff -> pp_print_string ppf "<->"

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
  let initials = uppercase_initials (strip_crdt_suffix mod_name) in
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

let rec unitify_proof_term = function
  | TEcst (Cbool true) -> TEcst Cnone
  | TEif (c, e1, e2)   -> TEif (c, unitify_proof_term e1, unitify_proof_term e2)
  | TEmatch (es, cases) ->
      TEmatch (es, List.map (fun (pats, b) -> (pats, unitify_proof_term b)) cases)
  | other -> other

let record_class_name decls n =
  if List.exists (function TDtype (name, TTRecord _, _, _) -> name = n | _ -> false) decls
  then String.split_on_char '_' n |> List.map String.capitalize_ascii |> String.concat ""
  else n

let camel_case n =
  match String.split_on_char '_' n with
  | [] -> n
  | first :: rest -> String.concat "" (first :: List.map String.capitalize_ascii rest)

let parse_class_directive attr =
  let s = String.trim attr in
  let s =
    if String.length s >= 3 && String.lowercase_ascii (String.sub s 0 3) = "vfx"
    then String.trim (String.sub s 3 (String.length s - 3))
    else s
  in
  match String.split_on_char ':' s with
  | kw :: (_ :: _ as rest) when String.trim kw = "class" ->
      Some (String.concat ":" rest
            |> String.split_on_char ','
            |> List.map String.trim
            |> List.filter (fun s -> s <> ""))
  | _ -> None

let class_directive_records decls =
  List.filter_map (function
    | TDtype (rname, TTRecord fields, _, Some attr) when rname <> name_payload ->
        (match parse_class_directive attr with
         | None -> None
         | Some names -> Some (rname, fields, names))
    | _ -> None) decls

let resolve_class_methods decls rname names =
  List.map (fun name ->
    match List.find_opt (function
      | TDval (fn, _, _, _) -> fn.fn_name = name
      | _ -> false) decls
    with
    | Some (TDval (fn, body, _, _)) ->
        if fn.fn_params = [] || (List.hd fn.fn_params).v_tp <> TTModuleRecord rname then
          failwith (Printf.sprintf
            "'%s' listed as a method of '%s' but its first parameter isn't a '%s'" name rname rname)
        else if List.exists (fun p -> p.v_tp = TTModuleRecord name_payload) fn.fn_params then
          failwith (Printf.sprintf
            "'%s' listed as a method of '%s' but it also takes a payload parameter" name rname)
        else (fn, body)
    | _ -> failwith (Printf.sprintf
        "'%s' listed as a method of '%s' but no such function is declared" name rname)
  ) names

let behavioral_aux_records decls =
  List.map (fun (rname, fields, names) -> (rname, fields, resolve_class_methods decls rname names))
    (class_directive_records decls)

let rec vfx_type_of_ttp ?(elem_name = "V") = function
  | TTInt -> "Int"
  | TTBool -> "Boolean"
  | TTModuleRecord m -> m
  | TTMap (k, v) -> Format.sprintf "Map[%s, %s]" (vfx_type_of_ttp ~elem_name k) (vfx_type_of_ttp ~elem_name v)
  | TTSet t  -> Printf.sprintf "Set[%s]" (vfx_type_of_ttp ~elem_name t)
  | TTAbstract _ -> elem_name
  | _ -> "Any"

let rec pp_vfx_texpr_simple ppf = function
  | TEvar v -> Format.pp_print_string ppf v.v_name
  | TEcall (fn, []) -> Format.fprintf ppf "%s()" fn.fn_name
  | TEcall (fn, args) ->
      Format.fprintf ppf "%s(%a)" fn.fn_name
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
           pp_vfx_texpr_simple) args
  | TEif (c, e1, e2) ->
      Format.fprintf ppf "if (%a) %a else %a"
        pp_vfx_texpr_simple c pp_vfx_texpr_simple e1 pp_vfx_texpr_simple e2
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
  | TEcall ({ fn_name = "set.diff"; _ }, [a; b]) ->
      let a' = rw_vfx_set_expr a and b' = rw_vfx_set_expr b in
      TEvar { v_name = Format.asprintf "%a.diff(%a)" pp_vfx_texpr_simple a' pp_vfx_texpr_simple b';
              v_tp   = TTBool }
  | TEcall ({ fn_name = "set.empty"; _ }, _) | TEvar { v_name = "set.empty"; _ } ->
      TEvar { v_name = "set.empty"; v_tp = TTBool }
  | TEnot e            -> TEnot (rw_vfx_set_expr e)
  | TEneg e            -> TEneg (rw_vfx_set_expr e)
  | TErequires (req, b) -> TErequires (rw_vfx_set_expr req, rw_vfx_set_expr b)
  | TErequires_vfx (req, b) -> TErequires_vfx (rw_vfx_set_expr req, rw_vfx_set_expr b)
  | TEif (c, e1, e2)   -> TEif (rw_vfx_set_expr c, rw_vfx_set_expr e1, rw_vfx_set_expr e2)
  | TEbinop (op, l, r) -> TEbinop (op, rw_vfx_set_expr l, rw_vfx_set_expr r)
  | TEcall (fn, args)  -> TEcall (fn, List.map rw_vfx_set_expr args)
  | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw_vfx_set_expr e)) fields)
  | TEfield (e, f)     -> TEfield (rw_vfx_set_expr e, f)
  | TEmatch (es, cases) -> TEmatch (List.map rw_vfx_set_expr es,
                            List.map (fun (pats, b) -> (pats, rw_vfx_set_expr b)) cases)
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

let rec map_texpr f expr =
  let descended = match expr with
    | TEbinop (op, l, r) -> TEbinop (op, map_texpr f l, map_texpr f r)
    | TEnot e            -> TEnot (map_texpr f e)
    | TEneg e            -> TEneg (map_texpr f e)
    | TErequires (req, b) -> TErequires (map_texpr f req, map_texpr f b)
    | TErequires_vfx (req, b) -> TErequires_vfx (map_texpr f req, map_texpr f b)
    | TEif (c, e1, e2)   -> TEif (map_texpr f c, map_texpr f e1, map_texpr f e2)
    | TEfield (e, field) -> TEfield (map_texpr f e, field)
    | TEcall (fn, args)  -> TEcall (fn, List.map (map_texpr f) args)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, map_texpr f e)) fields)
    | TEmatch (es, cases) -> TEmatch (List.map (map_texpr f) es,
                              List.map (fun (pats, b) -> (pats, map_texpr f b)) cases)
    | TElet (n, v, b)     -> TElet (n, map_texpr f v, map_texpr f b)
    | TEforall (vs, b)    -> TEforall (vs, map_texpr f b)
    | TEexists (vs, b)    -> TEexists (vs, map_texpr f b)
    | other              -> other
  in
  f descended

let uses_int_int = ref false

let rec ttp_deps = function
  | TTMap (k, v)             -> ttp_deps k @ ttp_deps v
  | TTSet t                  -> ttp_deps t
  | TTModuleRecord name      -> [name]
  | TTRecord fields          -> List.concat_map (fun (_, t) -> ttp_deps t) fields
  | TTVariantArgs (_, ctors) -> List.concat_map (fun (_, t) -> ttp_deps t) ctors
  | TTInt | TTBool | TTAbstract _ | TTInvariant _ | TTVariant _ -> []

let topo_sort_decls_by_type_deps decls =
  let type_decls = List.filter_map (function
    | TDtype (name, ttp, _, _) as d -> Some (name, ttp, d)
    | _ -> None) decls in
  let non_type_decls = List.filter (function TDtype _ -> false | _ -> true) decls in
  let known_names = List.map (fun (n, _, _) -> n) type_decls in
  let visited = Hashtbl.create 16 in
  let result = ref [] in
  let rec visit (name, ttp, d) =
    if not (Hashtbl.mem visited name) then begin
      Hashtbl.add visited name true;
      let deps = List.filter (fun n -> n <> name && List.mem n known_names) (ttp_deps ttp) in
      List.iter (fun dep ->
        match List.find_opt (fun (n, _, _) -> n = dep) type_decls with
        | Some entry -> visit entry
        | None -> ()
      ) deps;
      result := d :: !result
    end
  in
  List.iter visit type_decls;
  (List.rev !result) @ non_type_decls
let uses_min_max = ref false
let uses_fset    = ref false
let uses_map     = ref false

let reset_uses () =
  uses_int_int := false;
  uses_min_max := false;
  uses_fset    := false;
  uses_map     := false

let rec scan_ttp = function
  | TTInt -> uses_int_int := true
  | TTMap (k, v)   -> uses_map := true; scan_ttp k; scan_ttp v
  | TTSet elem     -> uses_fset := true; scan_ttp elem
  | TTRecord fields -> List.iter (fun (_, t) -> scan_ttp t) fields
  | TTVariantArgs (_, ctors) -> List.iter (fun (_, t) -> scan_ttp t) ctors
  | _ -> ()

let rec scan_texpr = function
  | TEcall (fn, args) ->
      if fn.fn_name = "max" || fn.fn_name = "min" then begin
        uses_int_int := true;
        uses_min_max := true
      end;
      List.iter scan_texpr args
  | TEbinop (_, l, r) -> scan_texpr l; scan_texpr r
  | TEif (c, e1, e2) -> scan_texpr c; scan_texpr e1; scan_texpr e2
  | TEfield (e, _) -> scan_texpr e
  | TErecord fields -> List.iter (fun (_, e) -> scan_texpr e) fields
  | TEmatch (es, cases) -> List.iter scan_texpr es;
      List.iter (fun (_, b) -> scan_texpr b) cases
  | TErequires (req, body) -> scan_texpr req; scan_texpr body
  | TErequires_vfx (_req, body) -> scan_texpr body
  | _ -> ()

let scan_tmodl = function
  | TDtype (_, tp, _, _)      -> scan_ttp tp
  | TDval (fn, body, _, _) ->
      List.iter (fun v     -> scan_ttp v.v_tp) fn.fn_params;
      scan_ttp fn.fn_return;
      scan_texpr body
  | TDlemma (fn, body, _, ens) ->
      List.iter (fun v -> scan_ttp v.v_tp) fn.fn_params;
      scan_texpr body;
      List.iter scan_texpr ens
  | TDaxiom _ -> ()

let map_poly_names : (string * string) option ref = ref None
let axiom_target_types : (string, ttp) Hashtbl.t = Hashtbl.create 8

let is_map_poly_var_ttp tp =
  match !map_poly_names, tp with
  | Some (k, v), TTModuleRecord n -> n = k || n = v
  | _ -> false

let map_poly_types decls =
  let abstract_names = List.filter_map (function
    | TDtype (n, TTAbstract _, _, _) -> Some n
    | _ -> None) decls
  in
  List.fold_left (fun acc d -> match d with
    | TDtype ("payload", TTMap (TTModuleRecord k, TTModuleRecord v), _, _)
      when List.mem k abstract_names && List.mem v abstract_names ->
        Some (k, v)
    | _ -> acc) None decls

let rec pp_w3_ttp ppf = function
  | TTInt              -> pp_print_string ppf "int"
  | TTBool             -> pp_print_string ppf "bool"
  | TTMap (k, v)       -> fprintf ppf "map %a %a" pp_w3_ttp k pp_w3_ttp v
  | TTSet elem         -> fprintf ppf "fset %a" pp_w3_ttp elem
  | TTAbstract name    -> pp_print_string ppf name
  | TTRecord fields    -> fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:pp_sep_break
          (fun ppf (name, tp) -> fprintf ppf "%s: %a;" name pp_w3_ttp tp)) fields
  | TTInvariant names  -> pp_print_string ppf (String.concat " " names)
  | TTModuleRecord m   ->
      (match !map_poly_names with
       | Some (k, v) when m = k || m = v -> fprintf ppf "'%s" m
       | Some (k, v) when m = "t" || m = name_payload -> fprintf ppf "%s '%s '%s" m k v
       | _ -> pp_print_string ppf m)
  | TTVariant (name, _)    -> pp_print_string ppf name
  | TTVariantArgs (name, _) -> pp_print_string ppf name

let rec pp_w3_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEfield (e, f)     -> fprintf ppf "%a.%s" pp_w3_texpr_atom e f
  | TEcall ({ fn_name = "map.combine"; _ }, [m1; m2; TEvar { v_name = combine_fn; _ }]) ->
      fprintf ppf "(fun key -> %s (Map.get %a key) (Map.get %a key))"
        combine_fn pp_w3_texpr_atom m1 pp_w3_texpr_atom m2
  | TEbinop (op, l, r) ->
      fprintf ppf "@[<h>%a@ %a@ %a@]" pp_w3_texpr l pp_w3_binop op pp_w3_texpr r
  | TEnot e            ->
      fprintf ppf "not %a" pp_w3_texpr_atom e
  | TEneg e            ->
      fprintf ppf "(- %a)" pp_w3_texpr_atom e
  | TErequires (_, _)  ->
      failwith "requires clause only allowed at the top of a val body"
  | TErequires_vfx (_, _)  ->
      failwith "requires [@vfx] clause should have been stripped before reaching Why3"
  | TElet (name, value, body) ->
      fprintf ppf "@[<v>let %s =@;<1 2>@[<v>%a@]@,in@ %a@]" name pp_w3_texpr value pp_w3_texpr body
  | TEif (c, e1, e2)   ->
      let rec pp_chain first c e1 e2 =
        if not first then fprintf ppf "else ";
        fprintf ppf "if %a then@;<0 2>@[<v>%a@]@ " pp_w3_texpr c pp_w3_texpr e1;
        match e2 with
        | TEif (c2, e1', e2') -> pp_chain false c2 e1' e2'
        | _ -> fprintf ppf "else@;<0 2>@[<v>%a@]" pp_w3_texpr e2
      in
      fprintf ppf "@[<v>"; pp_chain true c e1 e2; fprintf ppf "@]"
  | TEcall (fn, [])    ->
      fprintf ppf "%s ()" fn.fn_name
  | TEcall (fn, args)  ->
      fprintf ppf "@[<h>%s@ %a@]" fn.fn_name
        (pp_print_list ~pp_sep:pp_sep_space pp_w3_texpr_atom) args
  | TErecord fields    ->
      fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ";@ ")
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_w3_texpr e)) fields
  | TEmatch (es, cases)  ->
      fprintf ppf "@[<v>match %a with@ %a@ end@]"
        (pp_print_list ~pp_sep:pp_sep_comma pp_w3_texpr) es
        (pp_print_list ~pp_sep:pp_sep_break
          (fun ppf (pats, body) ->
            fprintf ppf "@[<hv 2>| %a -> %a@]"
              (pp_print_list ~pp_sep:pp_sep_comma pp_w3_case_pat) pats
              pp_w3_texpr body)) cases
  | TEforall (vars, body) ->
      let rec group = function
        | [] -> []
        | v :: rest ->
            let same, other = List.partition (fun u -> u.v_tp = v.v_tp) rest in
            (v :: same, v.v_tp) :: group other
      in
      fprintf ppf "(forall %a. %a)"
        (pp_print_list ~pp_sep:pp_sep_comma
          (fun ppf (vs, tp) -> fprintf ppf "%a: %a"
              (pp_print_list ~pp_sep:pp_sep_space
                (fun ppf v -> pp_print_string ppf v.v_name)) vs pp_w3_ttp tp))
        (group vars)
        pp_w3_texpr body
  | TEexists (vars, body) ->
      let rec group = function
        | [] -> []
        | v :: rest ->
            let same, other = List.partition (fun u -> u.v_tp = v.v_tp) rest in
            (v :: same, v.v_tp) :: group other
      in
      fprintf ppf "(exists %a. %a)"
        (pp_print_list ~pp_sep:pp_sep_comma
          (fun ppf (vs, tp) -> fprintf ppf "%a: %a"
              (pp_print_list ~pp_sep:pp_sep_space
                (fun ppf v -> pp_print_string ppf v.v_name)) vs pp_w3_ttp tp))
        (group vars)
        pp_w3_texpr body

and pp_w3_case_pat ppf (ctor, binders) =
  match binders with
  | [] -> pp_print_string ppf ctor
  | _  -> fprintf ppf "%s %a" ctor
            (pp_print_list ~pp_sep:pp_sep_space
              (fun ppf -> function
                | Some v -> pp_print_string ppf v.v_name
                | None   -> pp_print_string ppf "_")) binders

and pp_w3_texpr_atom ppf e = match e with
  | TEcst _ | TEvar _ | TEfield _ -> pp_w3_texpr ppf e
  | _                             -> fprintf ppf "(%a)" pp_w3_texpr e

let pp_w3_tparams ppf params =
  let rec group = function
    | [] -> []
    | v :: rest ->
        let same, other = List.partition (fun u -> u.v_tp = v.v_tp) rest in
        (v :: same, v.v_tp) :: group other
  in
  pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
    (fun ppf (vs, tp) -> fprintf ppf "(%a: %a)"
        (pp_print_list ~pp_sep:pp_sep_space
          (fun ppf v -> pp_print_string ppf v.v_name)) vs pp_w3_ttp tp) ppf (group params)

let pp_w3_uses ppf () =
  if !uses_fset then
    fprintf ppf "use set.Fset@ @ ";
  if !uses_map then
    fprintf ppf "use map.Map@ @ use map.Const@ @ ";
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

let rewrite_texpr_for_aux ?(rewrite_fields=false) payload_vars body =
  let is_local_call fn_name = not (String.contains fn_name '.') in
  let rec rw expr = match expr with
    | TEvar v when List.mem v.v_name payload_vars ->
        TEvar { v with v_name = v.v_name ^ "." ^ name_payload }
    | TEvar v when rewrite_fields ->
        (match String.split_on_char '.' v.v_name with
         | obj :: rest when List.mem obj payload_vars ->
             TEvar { v with v_name = obj ^ "." ^ name_payload ^ "." ^ String.concat "." rest }
         | _ -> TEvar v)
    | TEcall (fn, args) when is_local_call fn.fn_name ->
        let expects_payload i =
          match List.nth_opt fn.fn_params i with
          | Some p -> p.v_tp = TTModuleRecord name_payload
          | None   -> false
        in
        TEcall (fn, List.mapi (fun i a -> match a with
          | TEvar v when expects_payload i && List.mem v.v_name payload_vars -> TEvar v
          | other -> rw other) args)
    | TEfield ((TEcall (fn, _) as call), field) when is_local_call fn.fn_name ->
        TEfield (TEfield (rw call, name_payload), field)
    | TEfield (e, field) -> TEfield (rw e, field)
    | TEbinop (op, l, r) -> TEbinop (op, rw l, rw r)
    | TEnot e            -> TEnot (rw e)
    | TEneg e            -> TEneg (rw e)
    | TErequires (req, b) -> TErequires (rw req, rw b)
    | TErequires_vfx (req, b) -> TErequires_vfx (rw req, rw b)
    | TEif (c, e1, e2)   -> TEif (rw c, rw e1, rw e2)
    | TEcall (fn, args)  -> TEcall (fn, List.map rw args)
    | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw e)) fields)
    | TEmatch (es, cases) -> TEmatch (List.map rw es, List.map (fun (pats, b) -> (pats, rw b)) cases)
    | TEforall (vars, b) -> TEforall (vars, rw b)
    | TEexists (vars, b) -> TEexists (vars, rw b)
    | other -> other
  in
  rw body

let w3_set_fn = function
  | "set.empty"    -> "Fset.empty"
  | "set.add"      -> "Fset.add"
  | "set.union"    -> "Fset.union"
  | "set.contains" -> "Fset.mem"
  | "set.subset"   -> "Fset.subset"
  | "set.cardinal" -> "Fset.cardinal"
  | other          -> other

let rw_w3_map_expr_call fn_name args rw =
  match fn_name, args with
  | "map.get", [key; m] ->
      TEcall ({ fn_name = "Map.get"; fn_params = []; fn_return = TTBool },
              [rw m; rw key])
  | "map.set", [key; v; m] ->
      TEcall ({ fn_name = "Map.set"; fn_params = []; fn_return = TTBool },
              [rw m; rw key; rw v])
  | "map.empty", [] | "map.empty", _ ->
      TEvar { v_name = "Map.const"; v_tp = TTBool }
  | "map.const", [default] ->
      TEcall ({ fn_name = "Const.const"; fn_params = []; fn_return = TTBool },
              [rw default])
  | _ ->
      TEcall ({ fn_name = fn_name; fn_params = []; fn_return = TTBool },
              List.map rw args)

let rec rw_w3_set_expr = function
  | TEcall ({ fn_name = "set.empty"; _ }, _) ->
      TEvar { v_name = "Fset.empty"; v_tp = TTBool }
  | TEvar { v_name = "set.empty"; _ } ->
      TEvar { v_name = "Fset.empty"; v_tp = TTBool }
  | TEcall ({ fn_name; _ }, args)
    when String.length fn_name > 4 && String.sub fn_name 0 4 = "map." ->
      rw_w3_map_expr_call fn_name args rw_w3_set_expr
  | TEcall (fn, args) ->
      TEcall ({ fn with fn_name = w3_set_fn fn.fn_name },
              List.map rw_w3_set_expr args)
  | TEvar v ->
      TEvar { v with v_name = w3_set_fn v.v_name }
  | TEnot e            -> TEnot (rw_w3_set_expr e)
  | TEneg e            -> TEneg (rw_w3_set_expr e)
  | TErequires (req, b) -> TErequires (rw_w3_set_expr req, rw_w3_set_expr b)
  | TErequires_vfx (req, b) -> TErequires_vfx (rw_w3_set_expr req, rw_w3_set_expr b)
  | TEif (c, e1, e2)   -> TEif (rw_w3_set_expr c, rw_w3_set_expr e1, rw_w3_set_expr e2)
  | TEbinop (op, l, r) -> TEbinop (op, rw_w3_set_expr l, rw_w3_set_expr r)
  | TErecord fields    -> TErecord (List.map (fun (n, e) -> (n, rw_w3_set_expr e)) fields)
  | TEfield (e, f)     -> TEfield (rw_w3_set_expr e, f)
  | TEmatch (es, cases) -> TEmatch (List.map rw_w3_set_expr es,
                            List.map (fun (pats, b) -> (pats, rw_w3_set_expr b)) cases)
  | TEforall (vars, b)  -> TEforall (vars, rw_w3_set_expr b)
  | TEexists (vars, b)  -> TEexists (vars, rw_w3_set_expr b)
  | other -> other

let pp_w3_aux_decl ppf = function
  | TDtype (name, TTVariant (_, ctors), _, _) ->
      fprintf ppf "@[type %s =@ %a@]" name
        (pp_print_list ~pp_sep:pp_sep_bar pp_print_string) ctors

  | TDtype (name, TTVariantArgs (_, ctors), _, _) ->
      let pp_ctor_tp ppf = function
        | TTRecord fields ->
            pp_print_list ~pp_sep:pp_sep_space
              (fun ppf (_, tp) -> pp_w3_ttp ppf tp) ppf fields
        | tp -> pp_w3_ttp ppf tp
      in
      fprintf ppf "@[type %s =@ %a@]" name
        (pp_print_list ~pp_sep:pp_sep_bar
          (fun ppf (ctor, tp) -> fprintf ppf "%s %a" ctor pp_ctor_tp tp)) ctors

  | TDtype ("payload", tp, _, _) ->
      (match !map_poly_names with
       | Some (k, v) ->
           fprintf ppf "@[type %s '%s '%s = %a@]" name_payload k v pp_w3_ttp tp;
           fprintf ppf "@ @ ";
           fprintf ppf "@[type t '%s '%s = { %s: %s '%s '%s; }@]" k v name_payload name_payload k v;
           fprintf ppf "@ @ ";
           fprintf ppf "@[<v 2>let function get_payload (a: t '%s '%s) : %s '%s '%s@ = a.%s@]"
             k v name_payload k v name_payload
       | None ->
           fprintf ppf "@[type %s = %a@]" name_payload pp_w3_ttp tp;
           fprintf ppf "@ @ ";
           fprintf ppf "@[type t = { %s: %s; }@]" name_payload name_payload;
           fprintf ppf "@ @ ";
           fprintf ppf "@[<v 2>let function get_payload (a: t) : %s@ = a.%s@]" name_payload name_payload)

  | TDtype (name, TTAbstract _, _, _)
    when (match !map_poly_names with Some (k, v) -> name = k || name = v | None -> false) ->
      ()

  | TDtype (name, TTAbstract _, _, _) ->
      fprintf ppf "@[type %s@]" name

  | TDtype (name, tp, _, _) ->
      fprintf ppf "@[type %s = %a@]" name pp_w3_ttp tp

  | TDval ({ fn_name = "init_state"; _ }, body, _, _) ->
      let inner = match body with
        | TErecord fields ->
            (match List.assoc_opt name_payload fields with
             | Some v -> rw_w3_set_expr v
             | None   -> rw_w3_set_expr body)
        | other -> rw_w3_set_expr other
      in
      let t_tp = match !map_poly_names with
        | Some (k, v) -> Printf.sprintf "t '%s '%s" k v
        | None -> "t"
      in
      fprintf ppf "@[<v 2>let ghost function %s () : %s@ = { %s = %a }@]"
        name_create t_tp name_payload pp_w3_texpr inner
  | TDlemma (fn, body, variant_opt, ensures) ->
      let pvars = payload_param_names fn in
      let body' = rw_w3_set_expr (rewrite_texpr_for_aux ~rewrite_fields:true pvars body) in
      let body' = unitify_proof_term body' in
      let tparams = List.map (fun v ->
        if v.v_tp = TTModuleRecord name_payload
        then { v with v_tp = TTModuleRecord "t" }
        else v) fn.fn_params in
      let is_rec = variant_opt <> None in
      let let_kw = if is_rec then "let rec lemma" else "let lemma" in
      fprintf ppf "@[<v 2>%s %s %a" let_kw fn.fn_name pp_w3_tparams tparams;
      (match variant_opt with
       | Some vs -> fprintf ppf "@ variant { %s }" (String.concat ", " vs)
       | None -> ());
      List.iter (fun ens ->
        let ens' = rw_w3_set_expr (rewrite_texpr_for_aux ~rewrite_fields:true pvars ens) in
        fprintf ppf "@ ensures { %a }" pp_w3_texpr ens') ensures;
      fprintf ppf "@ = %a@]" pp_w3_texpr body'
  | TDaxiom (kind, func) ->
      let tp = match Hashtbl.find_opt axiom_target_types func with
        | Some t -> t
        | None -> TTBool
      in
      (match kind with
       | "commutative" ->
           fprintf ppf "@[<v 2>axiom %s_commutative: forall v1 v2: %a.@ %s v1 v2 = %s v2 v1@]"
             func pp_w3_ttp tp func func
       | "idempotent" ->
           fprintf ppf "@[<v 2>axiom %s_idempotent: forall v: %a.@ %s v v = v@]"
             func pp_w3_ttp tp func
       | "associative" ->
           fprintf ppf "@[<v 2>axiom %s_associative: forall v1 v2 v3: %a.@ %s (%s v1 v2) v3 = %s v1 (%s v2 v3)@]"
             func pp_w3_ttp tp func func func func
       | "equivalence" ->
           fprintf ppf "@[<v 2>axiom %s_correct: forall v1 v2: %a.@ (%s v1 v2 /\\ %s v2 v1) <-> v1 = v2@]"
             func pp_w3_ttp tp func func
       | other ->
           fprintf ppf "(* unknown axiom: %s(%s) *)" other func)
  | TDval (fn, TEcst Cnone, _, _) when fn.fn_params = [] && is_map_poly_var_ttp fn.fn_return ->
      fprintf ppf "@[val function %s () : %a@]" fn.fn_name pp_w3_ttp fn.fn_return
  | TDval (fn, TEcst Cnone, _, _) when fn.fn_params = [] ->
      fprintf ppf "@[constant %s : %a@]" fn.fn_name pp_w3_ttp fn.fn_return
  | TDval (fn, TEcst Cnone, _, _) ->
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[predicate %s %a@]" fn.fn_name pp_w3_tparams fn.fn_params
      else
        fprintf ppf "@[val function %s %a : %a@]" fn.fn_name pp_w3_tparams fn.fn_params pp_w3_ttp fn.fn_return
  | TDval (fn, body, _, variant_opt) ->
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
      let rewritten = rw_w3_set_expr (rewrite_texpr_for_aux ~rewrite_fields:true pvars body) in
      let req_opt, rewritten = match rewritten with
        | TErequires (req, b) -> (Some req, b)
        | TErequires_vfx (_req, b) -> (None, b)
        | other -> (None, other)
      in
      let pp_req ppf () = match req_opt with
        | Some req -> fprintf ppf "requires { %a }@ " pp_w3_texpr req
        | None -> ()
      in
      let returns_t_or_payload =
        ret = TTModuleRecord "t" || ret = TTModuleRecord name_payload
      in
      let is_already_wrapped = function
        | TErecord [(n, _)] when n = name_payload -> true
        | _ -> false
      in
      let is_payload_tp tp = tp = TTModuleRecord name_payload || tp = TTModuleRecord "t" in
      let already_produces_payload = function
        | TErecord _          -> true
        | TEcall (fn, _)      -> is_payload_tp fn.fn_return
        | TEvar v              -> is_payload_tp v.v_tp
        | _                    -> false
      in
      let hoist_record_ifs e =
        let bindings = ref [] in
        let rec go = function
          | TErecord fields ->
              TErecord (List.map (fun (n, v) ->
                let v' = go v in
                match v' with
                | TEif _ ->
                    let name = "new_" ^ n in
                    bindings := !bindings @ [ (name, v') ];
                    (n, TEvar { v_name = name; v_tp = TTBool })
                | _ -> (n, v')
              ) fields)
          | other -> other
        in
        let e' = go e in
        (!bindings, e')
      in
      let finalize_leaf e =
        let (bindings, e') = hoist_record_ifs e in
        List.fold_right (fun (n, ifexpr) acc -> TElet (n, ifexpr, acc)) bindings e'
      in
      let rec wrap_leaves e =
        match e with
        | TEif (c, e1, e2) -> TEif (c, wrap_leaves e1, wrap_leaves e2)
        | TEmatch (scruts, cases) ->
            TEmatch (scruts, List.map (fun (pats, b) -> (pats, wrap_leaves b)) cases)
        | TErecord _ when not (is_already_wrapped e) -> finalize_leaf (TErecord [(name_payload, e)])
        | other when already_produces_payload other -> finalize_leaf other
        | other -> finalize_leaf (TErecord [(name_payload, other)])
      in
      let final_body = if returns_t_or_payload then wrap_leaves rewritten else rewritten in
      let pp_aux_match_arm ppf (pats, arm_body) =
        fprintf ppf "@[<hv 2>| %a -> %a@]"
          (pp_print_list ~pp_sep:pp_sep_comma pp_w3_case_pat) pats
          pp_w3_texpr arm_body
      in
      let is_rec = variant_opt <> None in
      let let_kw =
        if is_rec then "let rec ghost function"
        else if !map_poly_names <> None then "function"
        else if !uses_map then "let ghost function"
        else "let function"
      in
      if is_bool_ttp fn.fn_return then begin
        let pred_kw = if is_rec then "let rec ghost function" else "predicate" in
        match variant_opt with
        | Some vs ->
            fprintf ppf "@[<v 2>%s %s %a : bool@ "
              pred_kw fn.fn_name pp_w3_tparams tparams;
            fprintf ppf "%avariant { %s }@ = %a@]"
              pp_req () (String.concat ", " vs) pp_w3_texpr rewritten
        | None ->
            fprintf ppf "@[<v 2>predicate %s %a@ %a= %a@]"
              fn.fn_name pp_w3_tparams tparams pp_req () pp_w3_texpr rewritten
      end else begin
        match final_body, variant_opt with
        | TEmatch (es, cases), None ->
            fprintf ppf "@[<v 2>function %s %a : %a@ %a= @[<v>match %a with@ %a@ end@]@]"
              fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret
              pp_req ()
              (pp_print_list ~pp_sep:pp_sep_comma pp_w3_texpr) es
              (pp_print_list ~pp_sep:pp_sep_break pp_aux_match_arm) cases
        | _, Some vs ->
            fprintf ppf "@[<v 2>%s %s %a : %a@ %avariant { %s }@ = %a@]"
              let_kw fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret
              pp_req () (String.concat ", " vs) pp_w3_texpr final_body
        | _, None ->
            fprintf ppf "@[<v 2>%s %s %a : %a@ %a= %a@]"
              let_kw fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret pp_req () pp_w3_texpr final_body
      end

let translate_fn_name fn_name =
  match String.split_on_char '.' fn_name with
  | [m; f] when Hashtbl.mem module_registry m ->
      let (_, alias) = Hashtbl.find module_registry m in
      let f' = if f = name_init_state then name_create else f in
      alias ^ "." ^ f'
  | _ ->
      if fn_name = name_init_state then name_create else fn_name

let body_less_const_names decls =
  List.filter_map (function
    | TDval (fn, TEcst Cnone, _, _) when fn.fn_params = [] && is_map_poly_var_ttp fn.fn_return ->
        None
    | TDval (fn, TEcst Cnone, _, _) -> Some fn.fn_name
    | _ -> None) decls

let fix_w3_const_calls decls e =
  let names = body_less_const_names decls in
  map_texpr (function
    | TEcall ({ fn_name; _ }, []) when List.mem fn_name names ->
        TEvar { v_name = fn_name; v_tp = TTBool }
    | other -> other) e

let pp_w3_auxiliary ppf aux_mod intfs decls =
  reset_uses ();
  List.iter scan_tmodl decls;
  Hashtbl.reset axiom_target_types;
  List.iter (function
    | TDval (fn, _, _, _) ->
        (match fn.fn_params with
         | p :: _ -> Hashtbl.replace axiom_target_types fn.fn_name p.v_tp
         | [] -> ())
    | _ -> ()) decls;
  let poly = map_poly_types decls in
  map_poly_names := poly;
  let aux_only_exclude = List.filter_map (function
    | Ifunc (id, _, _) when id.id = name_equals -> Some id.id
    | _ -> None) intfs in
  let aux_decls = List.filter (function
    | TDval (fn, _, _, _) -> not (List.mem fn.fn_name aux_only_exclude)
    | TDtype (name, TTAbstract _, _, _) ->
        (match poly with Some (k, v) -> name <> k && name <> v | None -> true)
    | _ -> true) decls in
  let aux_decls = List.map (function
    | TDval (fn, body, a, b) when body <> TEcst Cnone ->
        TDval (fn, fix_w3_const_calls decls body, a, b)
    | other -> other) aux_decls in
  let ordered = topo_sort_decls_by_type_deps aux_decls in
  fprintf ppf "@[<v 2>module %s@ @ %a%a@]@ @ end@ " aux_mod pp_w3_uses ()
    (pp_print_list ~pp_sep:pp_sep_blank pp_w3_aux_decl) ordered;
  map_poly_names := None

let main_poly_names : (string * string) option ref = ref None

let pp_w3_main_decl ppf (aux_alias, _payload_tp, tmodl) =
  match tmodl with
  | TDtype ("payload", _, _, _) ->
      (match !main_poly_names with
       | Some (k, v) ->
           fprintf ppf "@[type %s = %s.%s %s %s@]" name_payload aux_alias name_payload k v;
           fprintf ppf "@ @ ";
           fprintf ppf "@[type t = %s.t %s %s@]" aux_alias k v
       | None ->
           fprintf ppf "@[type %s = %s.%s@]" name_payload aux_alias name_payload;
           fprintf ppf "@ @ ";
           fprintf ppf "@[type t = %s.t@]" aux_alias)

  | TDtype (name, TTAbstract _, _, _)
    when (match !main_poly_names with Some (k, v) -> name = k || name = v | None -> false) ->
      fprintf ppf "@[type %s@]" name

  | TDtype (name, _, _, _) ->
      fprintf ppf "@[type %s = %s.%s@]" name aux_alias name

  | TDval ({ fn_name = "init_state"; _ }, _, _, _) ->
      fprintf ppf "@[<v 2>let function get_payload (a: t) : %a@ = %s.get_payload a@]"
        pp_w3_ttp _payload_tp aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let ghost function %s () : t@ = %s.%s ()@]"
        name_create aux_alias name_create

  | TDval ({ fn_name = "equals"; _ }, _, _, _) ->
      pp_w3_equals_predicate ppf ()

  | TDval (fn, body, _, _) ->
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
      let req_opt = match body with
        | TErequires (req, _) -> Some (rw_w3_set_expr req)
        | _ -> None
      in
      let pp_req ppf () = match req_opt with
        | Some req -> fprintf ppf "requires { %a }@ " pp_w3_texpr req
        | None -> ()
      in
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[<v 2>predicate %s %a@ %a= %s.%s %a@]"
          fn.fn_name pp_w3_tparams tparams pp_req () aux_alias fn.fn_name param_names tparams
      else
        let let_kw =
          if !main_poly_names <> None then "function"
          else if !uses_map && fn.fn_name <> "get_payload" then "let ghost function"
          else "let function"
        in
        fprintf ppf "@[<v 2>%s %s %a : %a@ %a= %s.%s %a@]"
          let_kw fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret pp_req () aux_alias fn.fn_name param_names tparams
  | TDlemma _ -> ()
  | TDaxiom _ -> ()
let rec texpr_calls name = function
  | TEcall (fn, args) -> fn.fn_name = name || List.exists (texpr_calls name) args
  | TEbinop (_, l, r) -> texpr_calls name l || texpr_calls name r
  | TEnot e | TEneg e  -> texpr_calls name e
  | TEfield (e, _)     -> texpr_calls name e
  | TEif (c, e1, e2)   -> texpr_calls name c || texpr_calls name e1 || texpr_calls name e2
  | TErecord fields     -> List.exists (fun (_, e) -> texpr_calls name e) fields
  | TEmatch (es, cases) ->
      List.exists (texpr_calls name) es ||
      List.exists (fun (_, b) -> texpr_calls name b) cases
  | TErequires (r, b) | TErequires_vfx (r, b) -> texpr_calls name r || texpr_calls name b
  | TEforall (_, b) | TEexists (_, b) -> texpr_calls name b
  | TElet (_, v, b) -> texpr_calls name v || texpr_calls name b
  | _ -> false

let is_called_by_another_decl decls name =
  List.exists (function
    | TDval (fn, body, _, _) when fn.fn_name <> name -> texpr_calls name body
    | _ -> false) decls

let pp_w3_main ppf (main_mod, sig_name, aux_mod, aux_alias, intfs, decls) =
  reset_uses ();
  List.iter scan_tmodl decls;
  main_poly_names := map_poly_types decls;
  let payload_tp = List.fold_left (fun acc d -> match d with
    | TDtype ("payload", tp, _, _) -> tp
    | _ -> acc) TTInt decls in
  let required_names = interface_fn_names intfs in
  let all_decls = List.filter (function
    | TDtype _ -> true
    | TDval ({ fn_name; _ }, _, _, _) when List.mem fn_name required_names -> true
    | TDval ({ fn_name; _ }, _, _, _) -> not (is_called_by_another_decl decls fn_name)
    | TDlemma _ -> false
    | TDaxiom _ -> false) decls in
  fprintf ppf "@[<v 2>module %s : %s@ @ %ause %s as %s@ @ %a@]@ @ end@ "
    main_mod sig_name
    pp_w3_uses ()
    aux_mod aux_alias
    (pp_print_list ~pp_sep:pp_sep_blank
      (fun ppf d -> pp_w3_main_decl ppf (aux_alias, payload_tp, d))) all_decls;
  main_poly_names := None

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

let is_pure_set_payload decls =
  List.exists (function
    | TDtype ("payload", TTSet _, _, _) -> true
    | TDtype ("payload", TTRecord fields, _, _) ->
        fields <> [] &&
        List.for_all (fun (_, tp) -> match tp with TTSet _ -> true | _ -> false) fields
    | _ -> false) decls

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
      (pp_print_list ~pp_sep:pp_sep_semi
        (fun ppf (n, _) -> fprintf ppf "%s: fset 'v" n)) fields;
    let payload_fn_name = String.lowercase_ascii (String.sub aux_mod 0 3) ^ "_payload" in
    fprintf ppf "@[<v 2>val function %s (s1 s2: fset 'v) : fset 'v@ ensures { result = Fset.diff s1 s2 }@]@ @ "
      payload_fn_name;
    fprintf ppf "@[<v 2>let function get_payload (t: t 'v) : fset 'v@ = %s %a@]@ @ "
      payload_fn_name
      (pp_print_list ~pp_sep:pp_sep_space
        (fun ppf (n, _) -> fprintf ppf "t.%s" n)) fields;
    fprintf ppf "@[<v 2>let ghost function %s () : t 'v@ = { %a }@]@ @ "
      name_create
      (pp_print_list ~pp_sep:pp_sep_semi
        (fun ppf (n, _) -> fprintf ppf "%s = Fset.empty" n)) fields;
    List.iter (function
      | TDtype _ -> ()
      | TDval ({ fn_name = "init_state"; _ }, _, _, _) -> ()
      | TDval ({ fn_name = "equals"; _ }, _, _, _) -> ()
      | TDlemma _ -> ()
      | TDaxiom _ -> ()
      | TDval (fn, body, _, _) ->
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
      | TDval ({ fn_name = "init_state"; _ }, _, _, _) -> ()
      | TDval ({ fn_name = "equals"; _ }, _, _, _) -> ()
      | TDlemma _ -> ()
      | TDaxiom _ -> ()
      | TDval (fn, body, _, _) ->
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
  fprintf ppf "@]end@ "

let pp_w3_set_main ppf (main_mod, sig_name, aux_mod, aux_alias, elem_tp, _intfs, decls) =
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
  (match List.find_opt (function TDval ({ fn_name = "init_state"; _ }, _, _, _) -> true | _ -> false) decls with
   | Some _ ->
       fprintf ppf "@[<v 2>let function get_payload (a: t) : %s@ = %s.get_payload a@]@ @ "
         name_payload aux_alias;
       fprintf ppf "@[<v 2>let ghost function %s () : t@ = %s.%s ()@]@ @ "
         name_create aux_alias name_create
   | None -> ());
  List.iter (function
    | TDtype _ -> ()
    | TDval ({ fn_name = "init_state"; _ }, _, _, _) -> ()
    | TDval ({ fn_name = "equals"; _ }, _, _, _) ->
        pp_w3_equals_predicate ppf ();
        fprintf ppf "@ @ "
    | TDlemma _ -> ()
    | TDaxiom _ -> ()
    | TDval (fn, _, _, _) ->
        let tparams = List.map (fun v -> match v.v_tp with
          | TTModuleRecord p when p = name_payload -> { v with v_tp = TTModuleRecord "t" }
          | TTAbstract _ -> { v with v_tp = TTModuleRecord elem_name }
          | TTModuleRecord n when n = elem_name -> v
          | _ -> v) fn.fn_params in
        let param_names ppf ps =
          pp_print_list ~pp_sep:(fun ppf () -> pp_print_char ppf ' ')
            (fun ppf v -> pp_print_string ppf v.v_name) ppf ps
        in
        if is_bool_ttp fn.fn_return then
          fprintf ppf "@[<v 2>predicate %s %a@ = %s.%s %a@]@ @ "
            fn.fn_name pp_w3_tparams tparams aux_alias fn.fn_name param_names tparams
        else
          fprintf ppf "@[<v 2>function %s %a : t@ = %s.%s %a@]@ @ "
            fn.fn_name pp_w3_tparams tparams aux_alias fn.fn_name param_names tparams
  ) decls;
  fprintf ppf "@]end@ "

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
    pp_print_list ~pp_sep:pp_sep_blank
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
          (pp_print_list ~pp_sep:pp_sep_space pp_param_type) params
      else
        fprintf ppf "@[function %s %a : t@]" id.id
          (pp_print_list ~pp_sep:pp_sep_space pp_param_type) params
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
  pp_print_list ~pp_sep:pp_sep_blank
    pp_w3_intf_decl ppf payload_types;
  fprintf ppf "@ @ @[type t@]@ @ ";
  if other_types <> [] then begin
    pp_print_list ~pp_sep:pp_sep_blank
      pp_w3_intf_decl ppf other_types;
    fprintf ppf "@ @ "
  end;
  fprintf ppf "@[val ghost function %s () : t@]@ @ " name_create;
  fprintf ppf "@[val function get_payload (a: t) : %s@]@ @ " name_payload;
  pp_print_list ~pp_sep:pp_sep_blank
    pp_w3_intf_decl ppf funcs;
  fprintf ppf "@ @ ";
  pp_w3_equals_predicate ppf ();
  pp_w3_axioms ppf intfs;
  fprintf ppf "@]@ @ end@ "

let pp_w3_composite ppf (main_mod, sig_name, intfs, decls) =
  let source_mod = match get_composite_source decls with
    | Some m -> m
    | None -> failwith "no composite source for this module"
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
      | TDval ({ fn_name; _ }, body, _, _)  when fn_name = name_init_state -> (pf, inv, Some body)
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
    (pp_print_list ~pp_sep:pp_sep_semi
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
        (pp_print_list ~pp_sep:pp_sep_semi
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
        (pp_print_list ~pp_sep:pp_sep_semi
          (fun ppf f -> let (n, e) = rw_init_field f in
            fprintf ppf "%s = %a" n pp_w3_texpr e)) fields
  | _ -> ()
  end;

  let make_decl = List.find_opt
    (function TDval ({ fn_name; _ }, _, _, _) -> fn_name = name_make | _ -> false) decls in
  begin match make_decl with
  | Some (TDval (fn, body, _, _)) ->
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
    | TDlemma _ -> false
    | TDaxiom _ -> false
    | TDval ({ fn_name; _ }, _, _, _) ->
        fn_name <> name_init_state && fn_name <> name_make) decls in

  let pp_composite_decl ppf = function
    | TDval ({ fn_name = "equals"; _ }, _, _, _) ->
        pp_w3_equals_predicate ppf ()
    | TDval (fn, body, _, _) ->
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
    | TDval (fn, _, _, _) -> List.mem fn.fn_name intf_fns | _ -> false) other_decls in
  let extra_decls = List.filter (function
    | TDval (fn, _, _, _) -> not (List.mem fn.fn_name intf_fns) | _ -> false) other_decls in
  let ordered = extra_decls @ intf_decls in

  pp_print_list ~pp_sep:pp_sep_blank
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
      let is_cvrdt = sig_name = "CvRDT" in
      if set_elem_tp <> None && is_cvrdt then begin
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
        let decls = List.map (function
          | TDval (fn, body, a, b) when body <> TEcst Cnone -> TDval (fn, fix_w3_const_calls decls body, a, b)
          | other -> other) decls
        in
        List.iter scan_tmodl decls;
        let ordered = List.filter (function
          | TDval (_, _, Some _, _) -> false
          | _ -> true) (topo_sort_decls_by_type_deps decls) in
        let lemma_decls = List.filter (function TDlemma _ -> true | _ -> false) ordered in
        let non_lemma_decls = List.filter (function TDlemma _ -> false | _ -> true) ordered in
        fprintf ppf "@[<v 2>module %s : %s@ @ %a%a%a@ @]@ end@ "
          main_mod sig_name
          pp_w3_uses ()
          (pp_print_list ~pp_sep:pp_sep_blank
            (fun ppf d -> match d with
              | TDval ({ fn_name; _ }, _, _, _) when fn_name = name_equals ->
                  pp_w3_equals_predicate ppf ()
              | TDlemma _ -> ()
              | _ -> pp_w3_aux_decl ppf d)) non_lemma_decls
          (fun ppf ls -> if ls <> [] then begin
            fprintf ppf "@ @ ";
            pp_print_list ~pp_sep:pp_sep_blank
              (fun ppf d -> match d with
               | TDlemma (fn, body, variant_opt, ensures) ->
                   let pvars = payload_param_names fn in
                   let body' = rw_w3_set_expr (rewrite_texpr_for_aux ~rewrite_fields:true pvars body) in
                   let body' = unitify_proof_term body' in
                   let tparams = List.map (fun v ->
                     if v.v_tp = TTModuleRecord name_payload
                     then { v with v_tp = TTModuleRecord "t" }
                     else v) fn.fn_params in
                   let is_rec = variant_opt <> None in
                   let let_kw = if is_rec then "let rec lemma" else "let lemma" in
                   fprintf ppf "@[<v 2>%s %s %a" let_kw fn.fn_name pp_w3_tparams tparams;
                   (match variant_opt with
                    | Some vs -> fprintf ppf "@ variant { %s }" (String.concat ", " vs)
                    | None -> ());
                   List.iter (fun ens ->
                     let ens' = rw_w3_set_expr (rewrite_texpr_for_aux ~rewrite_fields:true pvars ens) in
                     fprintf ppf "@ ensures { %a }" pp_w3_texpr ens') ensures;
                   fprintf ppf "@ = %a@]" pp_w3_texpr body'
               | _ -> ()) ppf ls
          end) lemma_decls
      end

let pp_w3_tfile ppf defs =
  fprintf ppf "@[<v>%a@]@."
    (pp_print_list ~pp_sep:pp_sep_break pp_w3_tdef) defs

let write_w3_tfile fmt tfile = pp_w3_tfile fmt tfile

let change_first_char f s =
  if String.length s = 0 then s
  else String.make 1 (f s.[0]) ^ String.sub s 1 (String.length s - 1)

let capitalise s = change_first_char Char.uppercase_ascii s

let axiom_to_proof_name prop func = func ^ capitalise prop

let vfx_generic_suffix type_params =
  match type_params with
  | [] -> ""
  | _  -> "[" ^ String.concat ", " type_params ^ "]"

let pp_vfx_proof ?(type_params = []) ppf (prop, func) =
  let g = vfx_generic_suffix type_params in
  let t = "T" ^ g in
  match prop with
  | "commutative" ->
      fprintf ppf "  proof %s%s {@ " (axiom_to_proof_name prop func) g;
      fprintf ppf "    forall (x: %s, y: %s) {@ " t t;
      fprintf ppf "      (x.reachable() && y.reachable() && x.compatible(y)) =>: {@ ";
      fprintf ppf "        x.%s(y).equals(y.%s(x)) &&@ " func func;
      fprintf ppf "        x.%s(y).reachable()@ " func;
      fprintf ppf "      }@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "idempotent" ->
      fprintf ppf "  proof %s%s {@ " (axiom_to_proof_name prop func) g;
      fprintf ppf "    forall (x: %s) {@ " t;
      fprintf ppf "      x.reachable() =>: x.%s(x).equals(x)@ " func;
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "associative" ->
      fprintf ppf "  proof %s%s {@ " (axiom_to_proof_name prop func) g;
      fprintf ppf "    forall (x: %s, y: %s, z: %s) {@ " t t t;
      fprintf ppf "      ( x.reachable() && y.reachable() && z.reachable() &&@ ";
      fprintf ppf "          x.compatible(y) && x.compatible(z) && y.compatible(z) ) =>: {@ ";
      fprintf ppf "        x.%s(y).%s(z).equals(x.%s(y.%s(z))) &&@ " func func func func;
      fprintf ppf "        x.%s(y).%s(z).reachable()@ " func func;
      fprintf ppf "      }@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "equivalence" ->
      fprintf ppf "  proof %s%s {@ " (axiom_to_proof_name prop func) g;
      fprintf ppf "    forall (x: %s, y: %s) {@ " t t;
      fprintf ppf "      x.equals(y) == (x == y)@ ";
      fprintf ppf "    }@ ";
      fprintf ppf "  }"
  | "op_commutative" ->
      fprintf ppf "  proof op_commutative%s {@ " g;
      fprintf ppf "    forall (s1: %s, s2: %s, s3: %s, x: Op, y: Op) {@ " t t t;
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

let pp_vfx_is_a_cvrdt ?(type_params = []) ppf () =
  let g = vfx_generic_suffix type_params in
  let t = "T" ^ g in
  fprintf ppf "  proof is_a_CvRDT%s {@ " g;
  fprintf ppf "    forall(x: %s, y: %s, z: %s) {@ " t t t;
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

let pp_vfx_is_a_cmrdt ?(type_params = []) ppf () =
  let g = vfx_generic_suffix type_params in
  let t = "T" ^ g in
  let op = "Op" ^ g in
  fprintf ppf "  proof is_a_CmRDT%s {@ " g;
  fprintf ppf "    forall (s1: %s, s2: %s, s3: %s, x: %s, y: %s) {@ " t t t op op;
  fprintf ppf "      val msg1 = s1.prepare(x)@ ";
  fprintf ppf "      val msg2 = s2.prepare(y)@ ";
  fprintf ppf "      ( s1.reachable() && s2.reachable() && s3.reachable() &&@ ";
  fprintf ppf "          s1.enabledSrc(x) && s2.enabledSrc(y) &&@ ";
  fprintf ppf "            //s1.enabledDown(msg1) && s2.enabledDown(msg2) &&@ ";
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

let pp_vfx_cvrdt_proof1 ppf (name, _proof, _intfs) =
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CvRDT@ @ ";
  fprintf ppf "trait %sProof1[ T[A] <: CvRDT[T[A]] ] {@ " name;
  pp_vfx_is_a_cvrdt ~type_params:["S"] ppf ();
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"] ppf ("commutative", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"] ppf ("idempotent", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"] ppf ("associative", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"] ppf ("equivalence", "compare");
  fprintf ppf "@ ";
  fprintf ppf "}@]@."

let pp_vfx_compatible_commutes ppf type_params =
  let g = vfx_generic_suffix type_params in
  let t = "T" ^ g in
  fprintf ppf "  proof compatibleCommutes%s {@ " g;
  fprintf ppf "    forall (x: %s, y: %s) {@ " t t;
  fprintf ppf "      ( x.reachable() && y.reachable() ) =>: ( x.compatible(y) == y.compatible(x) )@ ";
  fprintf ppf "    }@ ";
  fprintf ppf "  }"

let pp_vfx_compare_correct ppf type_params =
  let g = vfx_generic_suffix type_params in
  let t = "T" ^ g in
  fprintf ppf "  proof compareCorrect%s {@ " g;
  fprintf ppf "    forall (x: %s, y: %s) {@ " t t;
  fprintf ppf "      x.equals(y) == (x == y)@ ";
  fprintf ppf "    }@ ";
  fprintf ppf "  }"

let pp_vfx_cvrdt_proof2 ppf (name, _proof, _intfs) =
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CvRDT@ @ ";
  fprintf ppf "trait %sProof2[ T[A, B] <: %s[T[A, B]] ] {@ " name name;
  pp_vfx_is_a_cvrdt ~type_params:["S"; "U"] ppf ();
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"; "U"] ppf ("commutative", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"; "U"] ppf ("idempotent", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_proof ~type_params:["S"; "U"] ppf ("associative", "merge");
  fprintf ppf "@ @ ";
  pp_vfx_compatible_commutes ppf ["S"; "U"];
  fprintf ppf "@ @ ";
  pp_vfx_compare_correct ppf ["S"; "U"];
  fprintf ppf "@ ";
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

let pp_vfx_cmrdt_proof1 ppf (name, _proof, _intfs) =
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CmRDT@ @ ";
  fprintf ppf "trait %sProof1[Op[A], Msg[A], T[A] <: CmRDT[Op[A], Msg[A], T[A]]] {@ " name;
  pp_vfx_is_a_cmrdt ~type_params:["S"] ppf ();
  fprintf ppf "@ ";
  fprintf ppf "}@]@."

let pp_vfx_cmrdt_proof2 ppf (name, _proof, _intfs) =
  fprintf ppf "@[<v>import org.verifx.practical.crdts.CmRDT@ @ ";
  fprintf ppf "trait %sProof2[Op[A, B], Msg[A, B], T[A, B] <: %s[Op[A, B], Msg[A, B], T[A, B]]] {@ " name name;
  pp_vfx_is_a_cmrdt ~type_params:["S"; "U"] ppf ();
  fprintf ppf "@ ";
  fprintf ppf "}@]@."

let find_payload_vfx_attr decls =
  List.fold_left (fun acc d -> match d with
    | TDtype ("payload", _, _, Some ann) -> Some ann
    | _ -> acc) None decls

let find_variant_decls decls =
  List.filter_map (function
    | TDtype (name, TTVariant (_, ctors), _, _) -> Some (name, ctors)
    | TDtype (name, TTVariantArgs (_, ctors), _, _) -> Some (name, List.map fst ctors)
    | _ -> None) decls

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
  | Biff -> pp_print_string ppf "<=>"

let rewrite_vfx_method_body ?(field = "payload") self_param other_param class_name is_base body =
  map_texpr (function
    | TEvar v ->
        let name =
          match String.split_on_char '.' v.v_name with
          | [obj; f] when obj = self_param -> "this." ^ f
          | [obj; f] when obj = other_param -> "that." ^ f
          | [obj] when obj = self_param -> "this" ^ (if is_base then "." ^ field else "")
          | [obj] when obj = other_param -> "that" ^ (if is_base then "." ^ field else "")
          | _ -> v.v_name
        in
        TEvar { v with v_name = name }
    | TEcall ({ fn_name; _ } as fn, args) ->
        if fn_name = name_init_state || fn_name = "make" then
          TEcall ({ fn with fn_name = "new " ^ class_name }, args)
        else
          (match List.rev args with
           | TEvar { v_name = ("this" | "that"); _ } :: rest_rev
             when not (String.contains fn_name '.') ->
               TEcall ({ fn with fn_name = "this." ^ fn_name }, List.rev rest_rev)
           | _ -> TEcall (fn, args))
    | other -> other) body

let rewrite_receiver_calls receiver_names self_param other_param body =
  map_texpr (function
    | TEcall ({ fn_name; _ } as fn, [TEvar a1; TEvar a2])
      when List.mem fn_name receiver_names
        && not (String.contains fn_name '.')
        && (a1.v_name = self_param || a1.v_name = other_param)
        && (a2.v_name = self_param || a2.v_name = other_param)
        && a1.v_name <> a2.v_name ->
        let side v_name = if v_name = self_param then "this" else "that" in
        TEcall ({ fn with fn_name = side a1.v_name ^ "." ^ fn_name },
                [TEvar { a2 with v_name = side a2.v_name }])
    | other -> other) body

let rec pp_vfx_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEfield (e, f)     -> fprintf ppf "%a.%s" pp_vfx_texpr e f
  | TEbinop ((Band | Bor) as op, l, r) ->
      fprintf ppf "(%a %a@,%a)" pp_vfx_binop_operand l pp_vfx_binop op pp_vfx_binop_operand r
  | TEbinop (op, l, r) ->
      fprintf ppf "(%a %a %a)" pp_vfx_binop_operand l pp_vfx_binop op pp_vfx_binop_operand r
  | TEnot e            ->
      pp_print_string ppf "!";
      pp_vfx_texpr ppf e
  | TEneg e            ->
      fprintf ppf "-%a" pp_vfx_texpr e
  | TErequires (_, _)  ->
      failwith "requires clause only allowed at the top of a method body"
  | TErequires_vfx (_, _)  ->
      failwith "requires [@vfx] clause only allowed at the top of a method body"
  | TElet (name, value, body) ->
      fprintf ppf "@[<v>val %s = %a@,%a@]" name pp_vfx_texpr value pp_vfx_texpr body
  | TEif (c, e1, e2)   ->
      fprintf ppf "@[<v>if (%a) {@;<0 2>@[<v>%a@]@,} else {@;<0 2>@[<v>%a@]@,}@]"
        pp_vfx_texpr c pp_vfx_texpr e1 pp_vfx_texpr e2
  | TEcall ({ fn_name; _ }, args)
    when (String.length fn_name >= 5 && String.sub fn_name 0 5 = "this.")
      || (String.length fn_name >= 5 && String.sub fn_name 0 5 = "that.") ->
      fprintf ppf "%s(%a)" fn_name
        (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) args
  | TEcall ({ fn_name = "map.set"; _ }, [key_e; TEcall (empty_fn, []); target_e])
    when empty_fn.fn_params = [] ->
      fprintf ppf "%a.remove(%a)" pp_vfx_texpr target_e pp_vfx_texpr key_e
  | TEcall ({ fn_name = "map.combine"; _ }, [m1; m2; TEcall (combine_fn, [])]) ->
      let (p1, p2) = match combine_fn.fn_params with
        | a :: b :: _ -> (a, b)
        | _ -> failwith "map.combine's third argument must be a two-argument function"
      in
      fprintf ppf "%a.combine(%a, (%s: %s, %s: %s) => this.%s(%s, %s))"
        pp_vfx_texpr m1 pp_vfx_texpr m2
        p1.v_name (capitalise (vfx_type_of_ttp p1.v_tp))
        p2.v_name (capitalise (vfx_type_of_ttp p2.v_tp))
        combine_fn.fn_name p1.v_name p2.v_name
  | TEcall ({ fn_name; _ }, recv :: rest)
    when String.length fn_name > 0 && fn_name.[0] = '.' ->
      let method_name = String.sub fn_name 1 (String.length fn_name - 1) in
      fprintf ppf "%a.%s(%a)" pp_vfx_texpr recv method_name
        (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) rest
  | TEcall ({ fn_name; fn_return; _ }, args) when String.contains fn_name '.' ->
      let parts = String.split_on_char '.' fn_name in
      let mod_name = List.nth parts 0 in
      let method_name = List.nth parts 1 in
      let method_name =
        if mod_name = "set" && method_name = "cardinal" then "size"
        else if mod_name = "map" && method_name = "set" then "add"
        else method_name
      in
      if mod_name = "set" && method_name = "empty" then
        fprintf ppf "new Set()"
      else if mod_name = "map" && method_name = "const" then begin
        ignore args;
        fprintf ppf "new %s()" (vfx_type_of_ttp fn_return)
      end
      else if method_name = "init_state" || method_name = "create" then
        fprintf ppf "new %s()" mod_name
      else if method_name = "increment" then
        fprintf ppf "%a + %a" pp_vfx_texpr (List.nth args 1) pp_vfx_texpr (List.nth args 0)
      else if method_name = "decrement" then
        fprintf ppf "%a - %a" pp_vfx_texpr (List.nth args 1) pp_vfx_texpr (List.nth args 0)
      else if method_name = "merge" then
        failwith (Printf.sprintf "'%s.merge' wasn't rewritten to max/min before printing" mod_name)
      else if method_name = "compare" then
        fprintf ppf "%a == %a" pp_vfx_texpr (List.nth args 0) pp_vfx_texpr (List.nth args 1)
      else if method_name = "get_payload" || method_name = "value" then
        begin match args with
        | [a] -> fprintf ppf "%a.value()" pp_vfx_texpr a
        | _ -> fprintf ppf "%s.value(%a)" mod_name
                 (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) args
        end
      else
        let self_is_first = method_name = "merge" || method_name = "compare" || method_name = "equals" in
        if self_is_first then
          begin match args with
          | self_arg :: rest_args ->
              fprintf ppf "%a.%s(%a)" pp_vfx_texpr self_arg method_name
                (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) rest_args
          | [] -> fprintf ppf "%s.%s()" mod_name method_name
          end
        else
          let rev_args = List.rev args in
          begin match rev_args with
          | self_arg :: rest_rev ->
              let normal_args = List.rev rest_rev in
              fprintf ppf "%a.%s(%a)" pp_vfx_texpr self_arg method_name
                (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) normal_args
          | [] -> fprintf ppf "%s.%s()" mod_name method_name
          end
  | TEcall ({ fn_name; _ }, args) when fn_name = "max" || fn_name = "min" ->
    let scala_fn = if fn_name = "max" then "Math.max" else "Math.min" in
    fprintf ppf "%s(%a)" scala_fn
      (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) args
  | TEcall (fn, [])    ->
      fprintf ppf "%s()" fn.fn_name
  | TEcall (fn, args)  ->
      fprintf ppf "%s(%a)" fn.fn_name
        (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) args
  | TErecord fields    ->
      fprintf ppf "{ %a }"
        (pp_print_list ~pp_sep:pp_sep_comma
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_vfx_texpr e)) fields
  | TEmatch ([e], cases) ->
      fprintf ppf "@[<v>%a match {@;<0 2>@[<v>%a@]@,}@]" pp_vfx_texpr e
        (pp_print_list ~pp_sep:pp_sep_break
          (fun ppf (pats, body) ->
            let (name, binders) = match pats with
              | [p] -> p
              | _   -> assert false
            in
            let args = List.map (function
              | Some v -> v.v_name
              | None   -> "_") binders in
            fprintf ppf "case %s(%s) => %a" name (String.concat ", " args) pp_vfx_texpr body)) cases
  | TEmatch (_, _) ->
      failwith "VeriFx doesn't support matching on more than one value at once"
  | TEforall (vars, body) ->
      pp_quantifier ppf "forall" vars body
  | TEexists (vars, body) ->
      pp_quantifier ppf "exists" vars body

and pp_quantifier ppf quant_name vars body =
  let pp_binder ppf (v : var) =
    fprintf ppf "%s: %s" v.v_name (vfx_type_of_ttp v.v_tp)
  in
  fprintf ppf "@[<v>%s(%a) {@;<0 2>@[<v>%a@]@,}@]" quant_name
    (pp_print_list ~pp_sep:pp_sep_comma pp_binder) vars
    pp_vfx_texpr body

and pp_vfx_binop_operand ppf = function
  | TEif _ as e -> fprintf ppf "(%a)" pp_vfx_texpr e
  | e -> pp_vfx_texpr ppf e

let render_indented_vfx ~indent body =
  let text = Format.asprintf "@[<v>%a@]" pp_vfx_texpr body in
  String.concat ("\n" ^ indent) (String.split_on_char '\n' text)

let hoist_field_ifs fields =
  let bindings = ref [] in
  let rec replace fname = function
    | TEif _ as e ->
        let vname = "new" ^ String.capitalize_ascii fname in
        bindings := !bindings @ [(vname, e)];
        TEvar { v_name = vname; v_tp = TTBool }
    | TEbinop (op, l, r) -> TEbinop (op, replace fname l, replace fname r)
    | TEfield (e, f) -> TEfield (replace fname e, f)
    | TEnot e -> TEnot (replace fname e)
    | TEneg e -> TEneg (replace fname e)
    | other -> other
  in
  let new_fields = List.map (fun (n, v) -> (n, replace n v)) fields in
  (!bindings, new_fields)

let rewrite_record_method_calls decls e =
  let record_method_names =
    List.concat_map (fun (_, _, ms) -> List.map (fun (fn, _) -> fn.fn_name) ms)
      (behavioral_aux_records decls)
  in
  map_texpr (function
    | TEcall ({ fn_name; _ } as fn, (_ :: _ as args)) when List.mem fn_name record_method_names ->
        TEcall ({ fn with fn_name = "." ^ camel_case fn_name }, args)
    | other -> other) e

let pp_vfx_record_class ppf decls (rname, fields, methods) =
  let class_name = record_class_name decls rname in
  let self_tp = TTModuleRecord rname in
  let record_to_new e = map_texpr (function
    | TErecord flds'
      when List.length fields = List.length flds'
        && List.for_all (fun (n, _) -> List.mem_assoc n flds') fields ->
        let (bindings, flds'') = hoist_field_ifs flds' in
        let vals = List.map (fun (fname, _) -> List.assoc fname flds'') fields in
        let new_call = TEcall ({ fn_name = "new " ^ class_name; fn_params = []; fn_return = TTInt }, vals) in
        List.fold_right (fun (n, v) acc -> TElet (n, v, acc)) bindings new_call
    | other -> other) e
  in
  let field_str = String.concat ", "
    (List.map (fun (n, tp) -> Printf.sprintf "%s: %s" n (vfx_type_of_ttp tp)) fields)
  in
  fprintf ppf "class %s(%s) {\n" class_name field_str;
  List.iter (fun (fn, body) ->
    match fn.fn_params with
    | self_p :: rest ->
        let other_p, params = match rest with
          | p :: tl when p.v_tp = self_tp -> (Some p, tl)
          | _ -> (None, rest)
        in
        let other_name = match other_p with Some p -> p.v_name | None -> "" in
        let body = rewrite_record_method_calls decls body in
        let body' = rewrite_vfx_method_body self_p.v_name other_name class_name false body in
        let body' = record_to_new body' in
        let params_str = String.concat ", "
          ((match other_p with Some _ -> [Printf.sprintf "that: %s" class_name] | None -> [])
           @ List.map (fun p -> Printf.sprintf "%s: %s" p.v_name (vfx_type_of_ttp p.v_tp)) params)
        in
        let ret_str = if fn.fn_return = self_tp then class_name else vfx_type_of_ttp fn.fn_return in
        let body_text = render_indented_vfx ~indent:"    " body' in
        fprintf ppf "  def %s(%s): %s = {\n    %s\n  }\n\n"
          (camel_case fn.fn_name) params_str ret_str body_text
    | [] -> ()
  ) methods;
  fprintf ppf "}\n"

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
    | TEif (c, e1, e2) -> TEif (rw c, rw e1, rw e2)
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
        (pp_print_list ~pp_sep:pp_sep_comma
          (pp_vfx_vector_expr class_name)) args
  | other ->
      pp_vfx_texpr ppf other

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

let is_composite_payload fields =
  List.filter_map (fun (name, tp) ->
    match tp with
    | TTModuleRecord s when String.contains s '.' ->
        let composed_mod = List.hd (String.split_on_char '.' s) in
        Some (name, "Int", composed_mod)
    | _ -> None
  ) fields

let pp_vfx_set_module ppf (mod_name, _sig_name, elem_tp, decls) =
  let class_name = mod_name in
  let elem_name = match elem_tp with
    | TTAbstract n -> n
    | TTModuleRecord n -> n
    | _ -> "V"
  in
  let set_record_fields = get_set_record_fields decls in
  let is_record_set = set_record_fields <> None in
  fprintf ppf "import org.verifx.practical.crdts.CvRDT\n";
  let proof_class = "CvRDTProof1" in
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
    | TDval ({ fn_name = "init_state"; _ }, _, _, _) -> ()
    | TDval ({ fn_name = "equals"; _ }, _, _, _) -> ()
    | TDlemma _ -> ()
    | TDaxiom _ -> ()
    | TDval (fn, body, _, _) ->
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
              (pp_print_list ~pp_sep:pp_sep_comma pp_param) extra_params
              pp_body body'
          else
            if is_record_set then begin
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
                (pp_print_list ~pp_sep:pp_sep_comma pp_param) extra_params
                class_name
                (pp_print_list ~pp_sep:pp_sep_comma pp_vfx_texpr) field_vals
            end else
              fprintf ppf "  def %s(%a) = new %s(%a)\n"
                fn.fn_name
                (pp_print_list ~pp_sep:pp_sep_comma pp_param) extra_params
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
  | TEif (c, e1, e2) -> TEif (rewrite_minmax_to_method c, rewrite_minmax_to_method e1, rewrite_minmax_to_method e2)
  | other -> other

let pp_vfx_method is_base class_name ppf (fn: fn) body =
  let is_binop = fn.fn_name = "merge" || fn.fn_name = "compare" || fn.fn_name = "equals" in
  let self = if is_binop then (List.nth fn.fn_params 0).v_name
             else if List.length fn.fn_params >= 2 then (List.nth fn.fn_params 1).v_name else "a" in
  let other = if is_binop && List.length fn.fn_params >= 2 then (List.nth fn.fn_params 1).v_name else "" in
  let body' = rewrite_vfx_method_body self other class_name is_base body in
  let body' = if is_base && fn.fn_name = "merge" then rewrite_minmax_to_method body' else body' in
  let req_opt, body' = match body' with
    | TErequires (req, b) -> (Some req, b)
    | TErequires_vfx (req, b) -> (Some req, b)
    | other -> (None, other)
  in

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

  let pp_guarded ppf (pp_inner : Format.formatter -> unit) =
    match req_opt with
    | Some req ->
        let else_val = if is_bool_ttp fn.fn_return then "false" else "this" in
        fprintf ppf "if (%a) {\n      %t\n    } else {\n      %s\n    }"
          pp_vfx_texpr req pp_inner else_val
    | None -> pp_inner ppf
  in

  if fn.fn_name = "compare" then
    fprintf ppf "  def compare(that: %s): Boolean = {\n    %t\n  }\n\n" class_name
      (fun ppf -> pp_guarded ppf (fun ppf -> pp_top_level ppf body'))
  else if fn.fn_name = "merge" then
    fprintf ppf "  def merge(that: %s) = {\n    %t\n  }\n\n" class_name
      (fun ppf -> pp_guarded ppf (fun ppf -> wrap_expr ppf body'))
  else
    let args = List.filter (fun p -> p.v_name <> self) fn.fn_params in
    let pp_arg ppf (v: var) = fprintf ppf "%s: %s" v.v_name (vfx_type_of_ttp v.v_tp) in
    fprintf ppf "  def %s(%a) = {\n    %t\n  }\n\n" fn.fn_name
      (pp_print_list ~pp_sep:pp_sep_comma pp_arg) args
      (fun ppf -> pp_guarded ppf (fun ppf -> wrap_expr ppf body'))

let substitute_vars mapping body =
  map_texpr (function
    | TEvar v -> (try List.assoc v.v_name mapping with Not_found -> TEvar v)
    | other -> other) body

let rec resolve_map_combine decls join body =
  match body with
  | TEcall ({ fn_name = "map.combine"; _ }, [_; _; TEcall ({ fn_name; _ }, [])]) as combine_call
    when fn_name = join ->
      Some combine_call
  | TEcall ({ fn_name; _ }, args) ->
      (match List.find_opt (function
         | TDval (fn, _, _, _) -> fn.fn_name = fn_name
         | _ -> false) decls
       with
       | Some (TDval (callee, callee_body, _, _))
         when List.length callee.fn_params = List.length args ->
           let mapping = List.map2 (fun p a -> (p.v_name, a)) callee.fn_params args in
           resolve_map_combine decls join (substitute_vars mapping callee_body)
       | _ -> None)
  | _ -> None

let pp_vfx_map_poly_module ppf (mod_name, intfs, decls) =
  let (k, v) = match map_poly_types decls with
    | Some kv -> kv
    | None -> failwith "expected payload = map<k, v>"
  in
  let kt = capitalise k and vt = capitalise v in
  let translate_kv_type tp =
    if tp = TTModuleRecord k then kt
    else if tp = TTModuleRecord v then vt
    else vfx_type_of_ttp tp
  in

  let join = match List.find_map (function
      | TDval (fn, TEcst Cnone, _, _)
        when List.length fn.fn_params = 2
          && List.for_all (fun p -> p.v_tp = TTModuleRecord v) fn.fn_params
          && fn.fn_return = TTModuleRecord v -> Some fn.fn_name
      | _ -> None) decls
    with
    | Some n -> n
    | None -> failwith "no (v, v) -> v function found to merge values"
  in

  if not (List.exists (function
      | TDval (fn, TEcst Cnone, _, _) -> fn.fn_params = [] && fn.fn_return = TTModuleRecord v
      | _ -> false) decls)
  then failwith "no () -> v function found for the empty value";

  let axiom_kinds = List.filter_map (function
    | TDaxiom (kind, func) when func = join -> Some kind
    | _ -> None) decls
  in
  let value_axiom = function
    | "commutative" -> (["v1"; "v2"], Printf.sprintf "this.%s(v1, v2) == this.%s(v2, v1)" join join)
    | "idempotent"  -> (["v1"], Printf.sprintf "this.%s(v1, v1) == v1" join)
    | "associative" -> (["v1"; "v2"; "v3"],
        Printf.sprintf "this.%s(this.%s(v1, v2), v3) == this.%s(v1, this.%s(v2, v3))" join join join join)
    | other -> failwith (Printf.sprintf "unknown axiom '%s' on '%s'" other join)
  in
  let quantified_vars =
    ["v1"; "v2"; "v3"] |> List.filter (fun x -> List.exists (fun kind -> List.mem x (fst (value_axiom kind))) axiom_kinds)
  in

  let required_names = interface_fn_names intfs in
  let custom_ops = List.filter_map (function
    | TDval (fn, body, _, _)
      when not (List.mem fn.fn_name required_names)
        && List.length (List.filter (fun p -> p.v_tp = TTModuleRecord name_payload) fn.fn_params) = 1
        && List.length fn.fn_params > 1
        && not (is_called_by_another_decl decls fn.fn_name) ->
        Some (fn, body)
    | _ -> None) decls
  in
  let pp_custom_op ppf (fn, body) =
    let self_name = match List.find_opt (fun p -> p.v_tp = TTModuleRecord name_payload) fn.fn_params with
      | Some p -> p.v_name
      | None -> assert false
    in
    let other_params = List.filter (fun p -> p.v_name <> self_name) fn.fn_params in
    let params_str = String.concat ", "
      (List.map (fun p -> Printf.sprintf "%s: %s" p.v_name (translate_kv_type p.v_tp)) other_params)
    in
    let body = rewrite_receiver_calls required_names self_name "" body in
    let body' = rewrite_vfx_method_body ~field:"entries" self_name "" mod_name true body in
    fprintf ppf "  def %s(%s) = {\n    new %s(this.%s, %a)\n  }\n\n"
      fn.fn_name params_str mod_name join pp_vfx_texpr body'
  in

  let translated_merge_body =
    match List.find_opt (function TDval ({ fn_name = "merge"; _ }, _, _, _) -> true | _ -> false) decls with
    | Some (TDval (merge_fn, merge_body, _, _)) ->
        (match merge_fn.fn_params with
         | [self_p; other_p] ->
             (match resolve_map_combine decls join merge_body with
              | Some (TEcall (_, [TEvar m1; TEvar m2; _]) as combine_call)
                when (m1.v_name = self_p.v_name && m2.v_name = other_p.v_name)
                  || (m1.v_name = other_p.v_name && m2.v_name = self_p.v_name) ->
                  let combine_call = rewrite_receiver_calls required_names self_p.v_name other_p.v_name combine_call in
                  rewrite_vfx_method_body ~field:"entries" self_p.v_name other_p.v_name mod_name true combine_call
              | _ -> failwith "'merge' doesn't reduce to map.combine over the join function")
         | _ -> failwith "'merge' must take two payload parameters")
    | Some _ | None -> failwith "no 'merge' declared"
  in

  let compare_decl = List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _, _) -> true | _ -> false) decls in
  let equals_decl = List.find_opt (function TDval ({ fn_name = "equals"; _ }, _, _, _) -> true | _ -> false) decls in
  let rec contains_quantifier = function
    | TEforall _ | TEexists _ -> true
    | TEbinop (_, l, r) -> contains_quantifier l || contains_quantifier r
    | TEnot e | TEneg e -> contains_quantifier e
    | TEif (c, e1, e2) -> contains_quantifier c || contains_quantifier e1 || contains_quantifier e2
    | TEcall (_, args) -> List.exists contains_quantifier args
    | _ -> false
  in
  let pp_predicate ppf name fn body =
    match fn.fn_params with
    | [self_p; other_p] ->
        let body = rewrite_receiver_calls required_names self_p.v_name other_p.v_name body in
        let body' = rewrite_vfx_method_body ~field:"entries" self_p.v_name other_p.v_name mod_name true body in
        let def_kw = if name = "equals" then "override def" else "def" in
        fprintf ppf "  %s %s(that: %s[%s, %s]) = {\n    %a\n  }\n"
          def_kw name mod_name kt vt pp_vfx_texpr body'
    | _ -> failwith (Printf.sprintf "'%s' must take exactly two payload parameters" name)
  in
  let pp_compare_and_equals ppf () =
    match compare_decl, equals_decl with
    | Some (TDval (cfn, cbody, _, _)), Some (TDval (efn, ebody, _, _)) ->
        if contains_quantifier cbody && not (is_called_by_another_decl decls cfn.fn_name) then begin
          fprintf ppf "  def compare(that: %s[%s, %s]) = false\n" mod_name kt vt;
          pp_predicate ppf "equals" efn ebody
        end else begin
          pp_predicate ppf "compare" cfn cbody;
          fprintf ppf "\n";
          pp_predicate ppf "equals" efn ebody
        end
    | _ -> failwith "both 'compare' and 'equals' must be declared"
  in

  fprintf ppf "import org.verifx.practical.crdts.CvRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.CvRDTProof2\n\n";
  fprintf ppf "class %s[%s, %s](%s: (%s, %s) => %s, entries: Map[%s, %s] = new Map[%s, %s]()) extends CvRDT[%s[%s, %s]] {\n\n"
    mod_name kt vt join vt vt vt kt vt kt vt mod_name kt vt;
  fprintf ppf "  override def compatible(that: %s[%s, %s]) = {\n    this.%s == that.%s\n  }\n\n"
    mod_name kt vt join join;
  fprintf ppf "  override def reachable() = {\n";
  if quantified_vars = [] then
    fprintf ppf "    true\n"
  else begin
    fprintf ppf "    forall(%s) {\n"
      (String.concat ", " (List.map (fun x -> Printf.sprintf "%s: %s" x vt) quantified_vars));
    fprintf ppf "      %s\n"
      (String.concat " &&\n      " (List.map (fun kind -> snd (value_axiom kind)) axiom_kinds));
    fprintf ppf "    }\n"
  end;
  fprintf ppf "  }\n\n";
  List.iter (pp_custom_op ppf) custom_ops;
  fprintf ppf "  def merge(that: %s[%s, %s]) = {\n    new %s(this.%s, %a)\n  }\n\n"
    mod_name kt vt mod_name join pp_vfx_texpr translated_merge_body;
  pp_compare_and_equals ppf ();
  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends CvRDTProof2[%s]\n" mod_name mod_name

let pp_vfx_cvrdt_module ppf (mod_name, decls, all_modules) =
  let class_name = mod_name in
  let payload_decl = List.find_opt (function TDtype ("payload", _, _, _) -> true | _ -> false) decls in

  let is_composite, comp_fields, inv_opt =
    match payload_decl with
    | Some (TDtype (_, TTRecord fields, inv, _)) ->
        let cf = is_composite_payload fields in
        if cf <> [] then (true, cf, inv) else (false, [], inv)
    | _ -> (false, [], None)
  in
  let composed_mod_name = match comp_fields with
    | (_, _, m) :: _ -> Some m
    | [] -> None
  in
  let composite_merge_op = match composed_mod_name with
    | None -> None
    | Some m ->
        (match List.assoc_opt m all_modules with
         | None -> None
         | Some other_decls ->
             List.find_map (function
               | TDval ({ fn_name = "merge"; _ }, body, _, _) -> merge_uses_minmax body
               | _ -> None) other_decls)
  in
  let resolve_composite_calls e = map_texpr (function
    | TEcall ({ fn_name; _ } as fn, args) when String.contains fn_name '.' ->
        (match String.split_on_char '.' fn_name with
         | [m; "merge"] ->
             (match composite_merge_op with
              | Some op when m = Option.value composed_mod_name ~default:"" ->
                  TEcall ({ fn with fn_name = "this." ^ op }, args)
              | _ ->
                  failwith (Printf.sprintf "'%s' merge is neither max nor min, merge helper not supported" m))
         | _ -> TEcall (fn, args))
    | other -> other) e
  in

  let payload_ann = find_payload_vfx_attr decls in
  let is_vector = match payload_ann with Some ann when String.length ann > 0 -> true | _ -> false in

  fprintf ppf "import org.verifx.practical.crdts.CvRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.CvRDTProof\n\n";

  if is_composite then begin
    let ctor_args = String.concat ", " (List.map (fun (n, t, _) -> n ^ ": " ^ t) comp_fields) in
    fprintf ppf "class %s(%s) extends CvRDT[%s] {\n\n" class_name ctor_args class_name;
    (match inv_opt with
     | Some (_, inv_body) -> pp_vfx_composite_invariant ppf inv_body "a" class_name
     | None -> ());
    List.iter (function
      | TDval (fn, body, _, _) when fn.fn_name <> "init_state" && fn.fn_name <> "make" && fn.fn_name <> "equals" ->
          if fn.fn_name = "merge" then begin
            match composite_merge_op with
            | Some op ->
                let cmp = if op = "max" then ">=" else "<=" in
                fprintf ppf "  private def %s(a: Int, b: Int) = {\n    if (a %s b) a else b\n  }\n\n" op cmp
            | None ->
                failwith (Printf.sprintf "'%s' merge is neither max nor min, merge helper not supported"
                  (Option.value composed_mod_name ~default:"?"))
          end;
          pp_vfx_method false class_name ppf fn (resolve_composite_calls body)
      | _ -> ()) decls;
    fprintf ppf "}\n\n"
  end else if is_vector then begin
    let vector_type = match payload_ann with Some ann -> ann | None -> "Vector[Int]" in
    let elem_type = vector_element_type payload_ann in
    let tuple_type = Printf.sprintf "Tuple[%s, %s]" elem_type elem_type in
    fprintf ppf "class %s(payload: %s) extends CvRDT[%s] {\n\n" class_name vector_type class_name;
    List.iter (function
      | TDval (fn, body, Some idx_name, _) ->
          pp_vfx_vector_fn ppf class_name fn.fn_name idx_name body fn.fn_params;
          fprintf ppf "\n"
      | _ -> ()) decls;
    pp_vfx_compute_value ppf ();
    fprintf ppf "\n  private def max(t: %s) = if (t.fst >= t.snd) t.fst else t.snd\n\n" tuple_type;
    (match List.find_opt (function TDval ({ fn_name = "merge"; _ }, _, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _, _)) ->
         let self  = match fn.fn_params with v :: _ -> v.v_name | [] -> "a" in
         let other = match fn.fn_params with _ :: v :: _ -> v.v_name | _ -> "b" in
         let body' = rewrite_vfx_vector_body self other body in
         fprintf ppf "  def merge(that: %s): %s = %a\n\n" class_name class_name (pp_vfx_vector_expr class_name) body'
     | _ -> ());
    (match List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _, _)) ->
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
    let merge_decl = List.find_opt (function TDval ({ fn_name = "merge"; _ }, _, _, _) -> true | _ -> false) decls in
    let minmax_op = match merge_decl with
      | Some (TDval (_, body, _, _)) -> merge_uses_minmax body
      | _ -> None
    in
    fprintf ppf "class %s(payload: %s) extends CvRDT[%s] {\n\n" class_name base_type class_name;

    List.iter (function
      | TDval (fn, body, _, _)
        when fn.fn_name <> "init_state" && fn.fn_name <> "equals"
          && fn.fn_name <> "merge" && fn.fn_name <> "compare" ->
          pp_vfx_method true class_name ppf fn body
      | _ -> ()) decls;

    let has_value = List.exists (function
      | TDval ({ fn_name = "value"; _ }, _, _, _) -> true | _ -> false) decls in
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
     | Some (TDval (fn, body, _, _)) -> pp_vfx_method true class_name ppf fn body
     | _ -> ());
    (match List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _, _) -> true | _ -> false) decls with
     | Some (TDval (fn, body, _, _)) -> pp_vfx_method true class_name ppf fn body
     | _ -> ());

    fprintf ppf "}\n\n"
  end;

  fprintf ppf "object %s extends CvRDTProof[%s]\n" class_name class_name

let lowercase_first s = change_first_char Char.lowercase_ascii s

let pp_vfx_cmrdt_helper ppf class_name payload_field state_param ((pats : tcase list), body) =
  let ctor = match pats with [(c, _)] -> c | _ -> failwith "expected exactly one case" in
  let helper_name = lowercase_first ctor in
  let body' = rewrite_vfx_method_body state_param "" class_name false body in
  fprintf ppf "  def %s() = new %s(this.%s %a)\n"
    helper_name class_name payload_field
    (fun ppf e -> match e with
       | TEbinop (op, _, rhs) ->
           fprintf ppf "%a %a" pp_vfx_binop op pp_vfx_texpr rhs
       | _ ->
           pp_vfx_texpr ppf e) body'

let pp_vfx_effect_arm ppf ((pats : tcase list), (_body : texpr)) =
  let ctor = match pats with [(c, _)] -> c | _ -> failwith "expected exactly one case" in
  let helper_name = lowercase_first ctor in
  fprintf ppf "    case %s() => this.%s()\n" ctor helper_name

let pp_vfx_cmrdt_set_module ppf (mod_name, _sig_name, elem_tp, decls) =
  let class_name = mod_name in
  let elem_name = match elem_tp with
    | TTAbstract n -> n
    | TTModuleRecord n -> n
    | _ -> "V"
  in
  let (op_type_name, op_ctors_with_args) =
    List.fold_left (fun acc d -> match d with
      | TDtype (name, TTVariantArgs (_, ctors), _, _) -> (name, ctors)
      | TDtype (name, TTVariant (_, ctors), _, _) ->
          (name, List.map (fun c -> (c, TTAbstract elem_name)) ctors)
      | _ -> acc) ("Operation", []) decls
  in
  let set_fields = match get_set_record_fields decls with
    | Some fields -> List.map fst fields
    | None -> ["set"]
  in
  let execute_info = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "execute"; fn_params; _ }, body, _, _) ->
        let state_param = match fn_params with
          | _ :: v :: _ -> v.v_name
          | v :: _      -> v.v_name
          | []          -> "a"
        in
        Some (state_param, body)
    | _ -> acc) None decls
  in
  let lookup_info = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "lookup"; fn_params; _ }, body, _, _) ->
        let elem_param = match fn_params with
          | v :: _ -> v.v_name | [] -> "v"
        in
        Some (elem_param, body)
    | _ -> acc) None decls
  in
  fprintf ppf "import org.verifx.practical.crdts.CmRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.CmRDTProof1\n\n";
  if op_ctors_with_args <> [] then begin
    fprintf ppf "object %s {\n" op_type_name;
    fprintf ppf "  enum %s[%s] {\n" op_type_name elem_name;
    fprintf ppf "    %s\n"
      (String.concat " | "
        (List.map (fun (c, tp) ->
          Printf.sprintf "%s(e: %s)" c (vfx_type_of_ttp ~elem_name tp)
        ) op_ctors_with_args));
    fprintf ppf "  }\n";
    fprintf ppf "}\n\n"
  end;
  let ctor_args = String.concat ", "
    (List.map (fun f ->
      Printf.sprintf "%s: Set[%s] = new Set[%s]()" f elem_name elem_name
    ) set_fields)
  in
  let op_with_param = Printf.sprintf "%s[%s]" op_type_name elem_name in
  fprintf ppf "class %s[%s](%s) extends CmRDT[%s, %s, %s[%s]] {\n"
    class_name elem_name ctor_args
    op_with_param op_with_param class_name elem_name;
  (match lookup_info with
   | Some (elem_param, body) ->
       let state_param = List.fold_left (fun acc d -> match d with
         | TDval ({ fn_name = "lookup"; fn_params; _ }, _, _, _) ->
             (match fn_params with _ :: v :: _ -> v.v_name | _ -> acc)
         | _ -> acc) "a" decls
       in
       let body' = rewrite_vfx_method_body state_param "" class_name false body in
       let body' = rw_vfx_set_expr body' in
       fprintf ppf "  def lookup(%s: %s) = %a\n\n" elem_param elem_name pp_vfx_texpr body';
       ignore elem_param
   | None -> ());
  (match execute_info with
   | Some (state_param, TEmatch (_, cases)) ->
       List.iter (fun (pats, body) ->
         let (ctor, binders) = match pats with
           | [p] -> p
           | _ -> failwith "execute must match on exactly one value"
         in
         let bound_var = match binders with
           | [Some v] -> v.v_name
           | [None]   -> "e"
           | []       -> "e"
           | _ -> failwith (Printf.sprintf
               "constructor '%s' has more than one field" ctor)
         in
         let helper_name = lowercase_first ctor in
         let body' = rewrite_vfx_method_body state_param "" class_name false body in
         let body' = rw_vfx_set_expr body' in
         let fields_opt = get_set_record_fields decls in
         let field_names = match fields_opt with
           | Some fs -> List.map fst fs | None -> ["set"]
         in
         let pp_body ppf b = match b with
           | TErecord flds ->
               let vals = List.map (fun fname ->
                 match List.assoc_opt fname flds with
                 | Some e -> Format.asprintf "%a" pp_vfx_texpr e
                 | None -> Printf.sprintf "this.%s" fname
               ) field_names in
               fprintf ppf "new %s(%s)" class_name (String.concat ", " vals)
           | other -> pp_vfx_texpr ppf other
         in
         fprintf ppf "  def %s(%s: %s) = %a\n"
           helper_name bound_var elem_name pp_body body'
       ) cases;
       fprintf ppf "\n"
   | _ -> ());
  List.iter (function
    | TDval (fn, body, Some _, _) ->
        let fn_name = fn.fn_name in
        let is_override = fn_name = "enabledSrc" in
        let is_binop = fn.fn_name = "compare" in
        let self_param = if is_binop
          then (match fn.fn_params with v :: _ -> v.v_name | [] -> "a")
          else (match fn.fn_params with _ :: v :: _ -> v.v_name | v :: _ -> v.v_name | [] -> "a")
        in
        let other_param = if is_binop && List.length fn.fn_params >= 2
          then (List.nth fn.fn_params 1).v_name else "" in
        let body' = rewrite_vfx_method_body self_param other_param class_name false body in
        let body' = rw_vfx_set_expr body' in
        let extra_params = List.filter (fun p ->
          p.v_name <> self_param && p.v_name <> other_param) fn.fn_params in
        let pp_param ppf (v: var) =
          let tp_str = match v.v_tp with
            | TTAbstract _ -> elem_name
            | TTModuleRecord n when n = elem_name -> elem_name
            | TTModuleRecord "operation" ->
                Printf.sprintf "%s[%s]" op_type_name elem_name
            | t -> vfx_type_of_ttp ~elem_name t
          in
          fprintf ppf "%s: %s" v.v_name tp_str
        in
        let def_kw = if is_override then "override def" else "def" in
        fprintf ppf "  %s %s(%a) = %a\n\n" def_kw fn_name
          (pp_print_list ~pp_sep:pp_sep_comma pp_param) extra_params
          pp_vfx_texpr body'
    | _ -> ()
  ) decls;
  fprintf ppf "  def prepare(op: %s) = op\n\n" op_with_param;
  fprintf ppf "  def effect(op: %s) = op match {\n" op_with_param;
  (match execute_info with
   | Some (_, TEmatch (_, cases)) ->
       List.iter (fun (pats, _) ->
         let (ctor, binders) = match pats with
           | [p] -> p
           | _ -> failwith "effect must match on exactly one value"
         in
         let bound_var = match binders with
           | [Some v] -> v.v_name
           | [None]   -> "e"
           | []       -> "e"
           | _ -> failwith (Printf.sprintf
               "constructor '%s' has more than one field, VeriFx output doesn't support that" ctor)
         in
         let helper_name = lowercase_first ctor in
         fprintf ppf "    case %s(%s) => this.%s(%s)\n" ctor bound_var helper_name bound_var
       ) cases
   | _ -> ());
  fprintf ppf "  }\n";
  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends CmRDTProof1[%s, %s, %s]\n"
    class_name op_type_name op_type_name class_name

let pp_vfx_cmrdt_module ppf (mod_name, decls) =
  let class_name = mod_name in
  let variants = find_variant_decls decls in
  let (op_type_name, op_ctors) = match variants with
    | (name, ctors) :: _ -> (name, ctors)
    | [] -> ("Operation", [])
  in
  let execute_info = List.fold_left (fun acc d -> match d with
    | TDval ({ fn_name = "execute"; fn_params; _ }, body, _, _) ->
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
    | TDval ({ fn_name = "init_state"; _ }, TErecord fields, _, _) ->
        (match List.assoc_opt payload_field fields with
         | Some (TEcst (Cint n)) -> Some (Int64.to_string n)
         | Some (TEcst (Cbool b)) -> Some (string_of_bool b)
         | _ -> acc)
    | TDval ({ fn_name = "init_state"; _ }, TEcst (Cint n), _, _) ->
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
   | Some (state_param, TEmatch (_, cases)) ->
       List.iter (pp_vfx_cmrdt_helper ppf class_name payload_field state_param) cases;
       fprintf ppf "\n"
   | _ -> fprintf ppf "\n");
  fprintf ppf "  def prepare(op: %s) = op\n\n" op_type_name;
  fprintf ppf "  def effect(op: %s) = op match {\n" op_type_name;
  (match execute_info with
   | Some (_, TEmatch (_, cases)) ->
       List.iter (pp_vfx_effect_arm ppf) cases
   | _ ->
       fprintf ppf "    (* no execute body found *)\n");
  fprintf ppf "  }\n";
  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends CmRDTProof[%s, %s, %s]\n"
    class_name op_type_name op_type_name class_name

let pp_vfx_cmrdt_record_module ppf (mod_name, _sig_name, decls, all_modules) =
  let behavioral_records = behavioral_aux_records decls in
  let record_method_names =
    List.concat_map (fun (_, _, ms) -> List.map (fun (fn, _) -> fn.fn_name) ms) behavioral_records
  in
  let derive_remove_method_name other_decls =
    let other_payload_fields =
      List.fold_left (fun acc d -> match d with
        | TDtype (n, TTRecord fields, _, _) when n = name_payload -> fields
        | _ -> acc) [] other_decls
    in
    let other_set_fields =
      List.filter_map (fun (n, tp) -> match tp with TTSet _ -> Some n | _ -> None)
        other_payload_fields
    in
    match other_set_fields with
    | [n1; n2] ->
        let execute_info =
          List.find_map (function
            | TDval ({ fn_name = "execute"; fn_params; _ }, TEmatch (_, cases), _, _) ->
                (match List.find_opt (fun (p : var) -> p.v_tp = TTModuleRecord name_payload) fn_params with
                 | Some self -> Some (self.v_name, cases)
                 | None -> None)
            | _ -> None) other_decls
        in
        (match execute_info with
         | None -> None
         | Some (self_name, cases) ->
             let is_untouched field = function
               | TEvar v -> v.v_name = self_name ^ "." ^ field
               | _ -> false
             in
             List.find_map (fun (pats, body) -> match pats, body with
               | [(ctor, _)], TErecord flds ->
                   (match List.assoc_opt n1 flds, List.assoc_opt n2 flds with
                    | Some v1, Some v2 when is_untouched n1 v1 && not (is_untouched n2 v2) ->
                        Some (lowercase_first ctor)
                    | _ -> None)
               | _ -> None) cases)
    | _ -> None
  in
  let class_name = mod_name in

  let op_type_names = List.filter_map (function
    | TDtype (name, (TTVariant _ | TTVariantArgs _), _, _) -> Some name
    | _ -> None) decls
  in
  let aux_records_raw = List.filter_map (function
    | TDtype (name, TTRecord fields, _, attr)
      when name <> name_payload && not (List.mem name op_type_names) ->
        Some (name, fields, attr)
    | _ -> None) decls
  in
  let aux_records = List.map (fun (n, f, _) -> (n, f)) aux_records_raw in
  let parse_directives s =
    let s = String.trim s in
    let s =
      if String.length s >= 3 && String.lowercase_ascii (String.sub s 0 3) = "vfx"
      then String.trim (String.sub s 3 (String.length s - 3))
      else s
    in
    String.split_on_char ';' s
    |> List.filter_map (fun part ->
         match String.split_on_char ':' part with
         | k :: (_ :: _ as rest) -> Some (String.trim k, String.trim (String.concat ":" rest))
         | _ -> None)
  in
  let abstract_type_names =
    List.filter_map (function TDtype (n, TTAbstract _, _, _) -> Some n | _ -> None) decls
  in
  let is_type_generic tp = match tp with
    | TTModuleRecord n -> List.mem n abstract_type_names
    | TTAbstract _ -> true
    | _ -> false
  in
  let generic_aux_record_names =
    List.filter_map (fun (n, fields, _) ->
      if List.exists (fun (_, tp) -> is_type_generic tp) fields then Some n else None
    ) aux_records_raw
  in
  let is_generic = abstract_type_names <> [] in
  let payload_attr = List.fold_left (fun acc d -> match d with
    | TDtype (n, TTRecord _, _, attr) when n = name_payload -> attr
    | _ -> acc) None decls
  in
  let payload_directives = match payload_attr with
    | Some a -> parse_directives a
    | None -> []
  in
  let compose_directive = match payload_directives with (k, v) :: _ -> Some (k, v) | [] -> None in
  let compose_class_name = Option.map fst compose_directive in
  let compose_remove_method = lazy (
    match compose_class_name with
    | Some cls ->
        (match List.assoc_opt cls all_modules with
         | Some other_decls ->
             (match derive_remove_method_name other_decls with
              | Some m -> m
              | None ->
                  failwith (Printf.sprintf "can't find the removal method for '%s'" cls))
         | None ->
             failwith (Printf.sprintf "module '%s' not found" cls))
    | None ->
        failwith "compose_remove_method called with no compose directive"
  ) in
  let compose_field_name = Option.map snd compose_directive in
  let generic_tag = if is_generic then "[V]" else "" in
  let has_source = List.exists (function TDtype ("source_op", _, _, _) -> true | _ -> false) decls in
  let base_name = strip_crdt_suffix mod_name in
  let op_type_name = if has_source then base_name ^ "Op" else "Operation" in
  let msg_type_name = if has_source then base_name ^ "Msg" else "Operation" in

  let get_ctors target_name =
    match List.find_map (function
      | TDtype (name, TTVariantArgs (_, ctors), _, _) when name = target_name ->
          Some (List.map (fun (c, tp) -> match tp with TTRecord fs -> (c, fs) | other -> (c, [("e", other)])) ctors)
      | TDtype (name, TTVariant (_, ctors), _, _) when name = target_name ->
          Some (List.map (fun c -> (c, [])) ctors)
      | _ -> None) decls
    with Some c -> c | None -> []
  in
  let op_ctors = if has_source then get_ctors "source_op" else get_ctors "operation" in
  let msg_ctors = get_ctors "operation" in
  let known_ctor_names = List.map fst op_ctors @ List.map fst msg_ctors in
  let new_ctor_prefix e = map_texpr (function
    | TEcall ({ fn_name; _ } as fn, args) when List.mem fn_name known_ctor_names ->
        TEcall ({ fn with fn_name = "new " ^ fn_name }, args)
    | other -> other) e
  in

  let rec local_tp tp = match tp with
    | TTInt  -> "Int"
    | TTBool -> "Boolean"
    | TTModuleRecord "source_op" -> op_type_name ^ generic_tag
    | TTModuleRecord "operation" -> msg_type_name ^ generic_tag
    | TTModuleRecord n when n = name_payload -> class_name ^ generic_tag
    | TTModuleRecord n when List.mem n abstract_type_names -> "V"
    | TTModuleRecord n when List.mem n generic_aux_record_names -> record_class_name decls n ^ "[V]"
    | TTModuleRecord n -> record_class_name decls n
    | TTMap (k, v) -> Printf.sprintf "Map[%s, %s]" (local_tp k) (local_tp v)
    | TTSet t -> Printf.sprintf "Set[%s]" (local_tp t)
    | TTAbstract _ -> "V"
    | _ -> "Any"
  in
  let payload_fields = List.fold_left (fun acc d -> match d with
    | TDtype (n, TTRecord fields, _, _) when n = name_payload -> fields
    | _ -> acc) [] decls
  in
  let set_field_pair =
    match compose_field_name with
    | None -> None
    | Some _ ->
        (match List.filter (fun (_, tp) -> match tp with TTSet _ -> true | _ -> false) payload_fields with
         | [(n1, TTSet elem_tp); (n2, _)] -> Some (n1, n2, elem_tp)
         | _ -> None)
  in

  let index_of pred lst =
    let rec go i = function [] -> None | x :: tl -> if pred x then Some i else go (i + 1) tl in
    go 0 lst
  in
  let body_less_consts = List.filter_map (function
    | TDval (fn, TEcst Cnone, _, _) -> Some fn.fn_name
    | _ -> None) decls
  in
  let local_fn_names = List.filter_map (function
    | TDval (fn, _, _, _) when fn.fn_name <> "execute" && not (List.mem fn.fn_name body_less_consts) -> Some fn.fn_name
    | _ -> None) decls
  in
  let self_positions = List.filter_map (function
    | TDval (fn, _, _, _) ->
        (match index_of (fun v -> v.v_tp = TTModuleRecord name_payload) fn.fn_params with
         | Some i -> Some (fn.fn_name, i)
         | None -> None)
    | _ -> None) decls
  in
  let fuel_elim_positions = List.filter_map (function
    | TDval (fn, body, _, Some [ vn ]) ->
        (match index_of (fun (p : var) -> p.v_name = vn) fn.fn_params with
         | Some i ->
             (match body with
              | TEif (TEbinop (Ble, TEvar { v_name; _ }, TEcst (Cint 0L)), _then, _else)
                when v_name = vn -> Some (fn.fn_name, i)
              | _ -> None)
         | None -> None)
    | _ -> None) decls
  in
  let strip_fuel_guard fn_name body =
    match List.assoc_opt fn_name fuel_elim_positions with
    | Some _ ->
        (match body with
         | TEif (TEbinop (Ble, TEvar _, TEcst (Cint 0L)), _then, _else) -> _else
         | other -> other)
    | None -> body
  in
  let forall_to_collection e =
    let rec flatten_and e = match e with
      | TEbinop (Band, l, r) -> flatten_and l @ flatten_and r
      | other -> [other]
    in
    let rebuild_and = function
      | [] -> TEcst (Cbool true)
      | x :: rest -> List.fold_left (fun acc c -> TEbinop (Band, acc, c)) x rest
    in
    let is_set_contains v = function
      | TEcall ({ fn_name = "set.contains"; _ }, [TEvar v'; set_expr]) when v'.v_name = v.v_name -> Some set_expr
      | _ -> None
    in
    let rec go = function
      | TEforall ([v], TEbinop (Bor, TEnot (TEcall ({ fn_name = "map.contains"; _ }, [TEvar v'; map_expr])), p))
        when v'.v_name = v.v_name ->
          let map_expr' = go map_expr in
          let value_name = v.v_name ^ "_v" in
          let rec subst_get = function
            | TEcall ({ fn_name = "map.get"; _ }, [TEvar v''; _]) when v''.v_name = v.v_name ->
                TEvar { v_name = value_name; v_tp = v.v_tp }
            | TEcall (fn, args) -> TEcall (fn, List.map subst_get args)
            | TEfield (e, f)     -> TEfield (subst_get e, f)
            | TEbinop (op, l, r) -> TEbinop (op, subst_get l, subst_get r)
            | TEnot e            -> TEnot (subst_get e)
            | TEneg e            -> TEneg (subst_get e)
            | TEif (c, e1, e2)   -> TEif (subst_get c, subst_get e1, subst_get e2)
            | other -> other
          in
          let p' = go (subst_get p) in
          TEvar { v_name = Format.asprintf "%a.forall((%s: %s, %s: %s) => %a)"
                    pp_vfx_texpr map_expr' v.v_name (local_tp v.v_tp) value_name (local_tp v.v_tp) pp_vfx_texpr p';
                  v_tp = TTBool }
      | TEforall ([v], TEbinop (Bor, TEnot guard, p))
        when (match List.filter_map (is_set_contains v) (flatten_and guard) with [ _ ] -> true | _ -> false) ->
          let conjuncts = flatten_and guard in
          let set_expr = List.hd (List.filter_map (is_set_contains v) conjuncts) in
          let rest = List.filter (fun c -> is_set_contains v c = None) conjuncts in
          let set_expr' = go set_expr and p' = go p in
          if rest = [] then
            TEvar { v_name = Format.asprintf "%a.forall((%s: %s) => %a)"
                      pp_vfx_texpr set_expr' v.v_name (local_tp v.v_tp) pp_vfx_texpr p';
                    v_tp = TTBool }
          else
            let q' = go (rebuild_and rest) in
            TEvar { v_name = Format.asprintf "%a.filter((%s: %s) => %a).forall((%s: %s) => %a)"
                      pp_vfx_texpr set_expr' v.v_name (local_tp v.v_tp) pp_vfx_texpr q'
                      v.v_name (local_tp v.v_tp) pp_vfx_texpr p';
                    v_tp = TTBool }
      | TEforall (vs, b) -> TEforall (vs, go b)
      | TEexists (vs, b) -> TEexists (vs, go b)
      | TEcall (fn, args)   -> TEcall (fn, List.map go args)
      | TEfield (e, f)      -> TEfield (go e, f)
      | TEbinop (op, l, r)  -> TEbinop (op, go l, go r)
      | TEnot e             -> TEnot (go e)
      | TEneg e             -> TEneg (go e)
      | TEif (c, e1, e2)    -> TEif (go c, go e1, go e2)
      | TErecord flds       -> TErecord (List.map (fun (n, v) -> (n, go v)) flds)
      | TEmatch (es, cases) -> TEmatch (List.map go es, List.map (fun (p, b) -> (p, go b)) cases)
      | TErequires (r, b)   -> TErequires (go r, go b)
      | TErequires_vfx (r, b)   -> TErequires_vfx (go r, go b)
      | other -> other
    in go e
  in

  let resolve_quantifier_types e =
    let pp_binder ppf (v : var) = fprintf ppf "%s: %s" v.v_name (local_tp v.v_tp) in
    let pp_vars = pp_print_list ~pp_sep:pp_sep_comma pp_binder in
    let rec go = function
      | TEforall (vars, b) ->
          let b' = go b in
          TEvar { v_name = Format.asprintf "@[<v>forall(%a) {@;<0 2>@[<v>%a@]@,}@]"
                    pp_vars vars pp_vfx_texpr b';
                  v_tp = TTBool }
      | TEexists (vars, b) ->
          let b' = go b in
          TEvar { v_name = Format.asprintf "@[<v>exists(%a) {@;<0 2>@[<v>%a@]@,}@]"
                    pp_vars vars pp_vfx_texpr b';
                  v_tp = TTBool }
      | TEcall (fn, args)   -> TEcall (fn, List.map go args)
      | TEfield (e, f)      -> TEfield (go e, f)
      | TEbinop (op, l, r)  -> TEbinop (op, go l, go r)
      | TEnot e             -> TEnot (go e)
      | TEneg e             -> TEneg (go e)
      | TEif (c, e1, e2)    -> TEif (go c, go e1, go e2)
      | TErecord flds       -> TErecord (List.map (fun (n, v) -> (n, go v)) flds)
      | TEmatch (es, cases) -> TEmatch (List.map go es, List.map (fun (p, b) -> (p, go b)) cases)
      | TErequires (r, b)   -> TErequires (go r, go b)
      | TErequires_vfx (r, b)   -> TErequires_vfx (go r, go b)
      | other -> other
    in go e
  in

  let const_field_map =
    match List.find_map (function
      | TDval ({ fn_name = "init_state"; _ }, TErecord flds, _, _) -> Some flds
      | _ -> None) decls
    with
    | Some flds ->
        List.filter_map (fun (fname, fval) -> match fval with
          | TEcall ({ fn_name = c; _ }, []) when List.mem c body_less_consts -> Some (c, fname)
          | TEvar { v_name = c; _ } when List.mem c body_less_consts -> Some (c, fname)
          | _ -> None) flds
    | None -> []
  in
  let rec collect_calls target_name e acc = match e with
    | TEcall ({ fn_name; _ }, args) when fn_name = target_name ->
        List.fold_left (fun acc a -> collect_calls target_name a acc) (args :: acc) args
    | TEcall (_, args) -> List.fold_left (fun acc a -> collect_calls target_name a acc) acc args
    | TEfield (e, _) -> collect_calls target_name e acc
    | TEbinop (_, l, r) -> collect_calls target_name r (collect_calls target_name l acc)
    | TEnot e | TEneg e -> collect_calls target_name e acc
    | TEif (c, e1, e2) ->
        collect_calls target_name e2 (collect_calls target_name e1 (collect_calls target_name c acc))
    | TErecord flds -> List.fold_left (fun acc (_, v) -> collect_calls target_name v acc) acc flds
    | TEmatch (es, cases) ->
        List.fold_left (fun acc (_, b) -> collect_calls target_name b acc)
          (List.fold_left (fun acc e -> collect_calls target_name e acc) acc es) cases
    | TErequires (r, b) -> collect_calls target_name b (collect_calls target_name r acc)
    | TErequires_vfx (r, b) -> collect_calls target_name b (collect_calls target_name r acc)
    | _ -> acc
  in
  let const_sourced_positions =
    List.filter_map (function
      | TDval (fn, _, _, _) when fn.fn_params <> [] && not (List.mem fn.fn_name body_less_consts) ->
          let all_calls =
            List.fold_left (fun acc d -> match d with
              | TDval (_, body, _, _) -> collect_calls fn.fn_name body acc
              | _ -> acc) [] decls
          in
          if all_calls = [] then None
          else
            let positions =
              List.mapi (fun i _ ->
                let vals = List.filter_map (fun args -> List.nth_opt args i) all_calls in
                if vals = [] || List.length vals <> List.length all_calls then None
                else
                  let consts = List.filter_map (function
                    | TEcall ({ fn_name = c; _ }, []) when List.mem c body_less_consts -> Some c
                    | TEvar { v_name = c; _ } when List.mem c body_less_consts -> Some c
                    | _ -> None) vals
                  in
                  if List.length consts = List.length vals then
                    match consts with
                    | c0 :: rest when List.for_all (( = ) c0) rest ->
                        (match List.assoc_opt c0 const_field_map with
                         | Some field -> Some (i, field)
                         | None -> None)
                    | _ -> None
                  else None
              ) fn.fn_params
              |> List.filter_map (fun x -> x)
            in
            if positions = [] then None else Some (fn.fn_name, positions)
      | _ -> None) decls
  in
  let add_this_prefix e = map_texpr (function
    | TEcall (fn, args) when List.mem fn.fn_name local_fn_names ->
        let drop_positions =
          (match List.assoc_opt fn.fn_name self_positions with Some i -> [i] | None -> [])
          @ (match List.assoc_opt fn.fn_name const_sourced_positions with
             | Some ps -> List.map fst ps | None -> [])
          @ (match List.assoc_opt fn.fn_name fuel_elim_positions with Some i -> [i] | None -> [])
        in
        let args' = List.filteri (fun j _ -> not (List.mem j drop_positions)) args in
        TEcall ({ fn with fn_name = "this." ^ fn.fn_name }, args')
    | other -> other) e
  in
  let self_param_name (fn : fn) =
    List.find_opt (fun v -> v.v_tp = TTModuleRecord name_payload) fn.fn_params
    |> Option.map (fun v -> v.v_name)
  in
  let other_param_name (fn : fn) =
    let payload_params = List.filter (fun v -> v.v_tp = TTModuleRecord name_payload) fn.fn_params in
    match payload_params with
    | _ :: (o : var) :: _ -> Some o.v_name
    | _ -> None
  in
  let rewrite_name old_name new_name e = map_texpr (function
    | TEvar v ->
        let prefix = old_name ^ "." in
        let plen = String.length prefix in
        if v.v_name = old_name then TEvar { v with v_name = new_name }
        else if String.length v.v_name > plen && String.sub v.v_name 0 plen = prefix then
          let rest = String.sub v.v_name plen (String.length v.v_name - plen) in
          TEvar { v with v_name = new_name ^ "." ^ rest }
        else TEvar v
    | other -> other) e
  in
  let composed_payload_fields =
    match set_field_pair, compose_field_name with
    | Some (n1, n2, _), Some cname ->
        List.filter_map (fun (n, tp) ->
          if n = n1 then Some (cname, TTBool)
          else if n = n2 then None
          else Some (n, tp)) payload_fields
    | _ -> payload_fields
  in
  let all_record_defs = (class_name, composed_payload_fields) :: aux_records in
  let annotate_empty_set ftp v = match ftp, v with
    | TTSet inner, TEcall ({ fn_name = "set.empty"; _ } as fn, []) ->
        TEcall ({ fn with fn_name = "new Set[" ^ vfx_type_of_ttp inner ^ "]" }, [])
    | _ -> v
  in
  let compose_added_removed e =
    match set_field_pair, compose_field_name, compose_class_name with
    | Some (n1, n2, _), Some cname, Some compose_class ->
        let this_n1 = "this." ^ n1 and this_n2 = "this." ^ n2 in
        let is_var name = function TEvar v -> v.v_name = name | _ -> false in
        let rec go e = match e with
          | TErecord flds when List.mem_assoc n1 flds && List.mem_assoc n2 flds ->
              let raw_added = List.assoc n1 flds and raw_removed = List.assoc n2 flds in
              let is_empty = function TEcall ({ fn_name = "set.empty"; _ }, []) -> true | _ -> false in
              let composed =
                if is_empty raw_added && is_empty raw_removed then
                  TEcall ({ fn_name = "new " ^ compose_class; fn_params = []; fn_return = TTBool }, [])
                else match raw_added, raw_removed with
                  | TEcall ({ fn_name = "set.add"; _ }, [x; base]), rem
                    when is_var this_n1 base && is_var this_n2 rem ->
                      TEcall ({ fn_name = "this." ^ cname ^ ".add"; fn_params = []; fn_return = TTBool }, [go x])
                  | add, TEcall ({ fn_name = "set.add"; _ }, [x; base])
                    when is_var this_n1 add && is_var this_n2 base ->
                      TEcall ({ fn_name = "this." ^ cname ^ "." ^ Lazy.force compose_remove_method; fn_params = []; fn_return = TTBool }, [go x])
                  | _ ->
                      TEcall ({ fn_name = "new " ^ compose_class; fn_params = []; fn_return = TTBool }, [go raw_added; go raw_removed])
              in
              let other_flds = List.filter (fun (n, _) -> n <> n1 && n <> n2) flds in
              TErecord ((cname, composed) :: List.map (fun (n, v) -> (n, go v)) other_flds)
          | TEbinop (Band, TEcall ({ fn_name = "set.contains"; _ }, [v1; b1]),
                           TEnot (TEcall ({ fn_name = "set.contains"; _ }, [v2; b2])))
            when is_var this_n1 b1 && is_var this_n2 b2
              && (match v1, v2 with TEvar a, TEvar b -> a.v_name = b.v_name | _ -> false) ->
              TEcall ({ fn_name = "this." ^ cname ^ ".lookup"; fn_params = []; fn_return = TTBool }, [go v1])
          | TEvar v when v.v_name = this_n1 -> TEvar { v with v_name = "this." ^ cname ^ "." ^ n1 }
          | TEvar v when v.v_name = this_n2 -> TEvar { v with v_name = "this." ^ cname ^ "." ^ n2 }
          | TEcall (fn, args)   -> TEcall (fn, List.map go args)
          | TEfield (e, f)      -> TEfield (go e, f)
          | TEbinop (op, l, r)  -> TEbinop (op, go l, go r)
          | TEnot e             -> TEnot (go e)
          | TEneg e             -> TEneg (go e)
          | TEif (c, e1, e2)    -> TEif (go c, go e1, go e2)
          | TErecord flds       -> TErecord (List.map (fun (n, v) -> (n, go v)) flds)
          | TEmatch (es, cases) -> TEmatch (List.map go es, List.map (fun (p, b) -> (p, go b)) cases)
          | TErequires (r, b)   -> TErequires (go r, go b)
          | TErequires_vfx (r, b)   -> TErequires_vfx (go r, go b)
          | TEforall (vars, b)  -> TEforall (vars, go b)
          | TEexists (vars, b)  -> TEexists (vars, go b)
          | other -> other
        in
        go e
    | _ -> e
  in
  let hoist_record_ifs_vfx e =
    let rec go = function
      | TErecord fields ->
          let processed = List.map (fun (n, v) ->
            let v' = go v in
            match v' with
            | TEif _ -> (n, `Hoisted ("new" ^ String.capitalize_ascii n, v'))
            | _ -> (n, `Plain v')
          ) fields in
          let bindings = List.filter_map (function
            | (_, `Hoisted (name, v)) -> Some (name, v)
            | _ -> None) processed in
          let final_fields = List.map (function
            | (n, `Hoisted (name, _)) -> (n, TEvar { v_name = name; v_tp = TTBool })
            | (n, `Plain v) -> (n, v)) processed in
          List.fold_right (fun (name, v) acc -> TElet (name, v, acc)) bindings (TErecord final_fields)
      | TEif (c, e1, e2)    -> TEif (c, go e1, go e2)
      | TEmatch (es, cases) -> TEmatch (es, List.map (fun (p, b) -> (p, go b)) cases)
      | TErequires (r, b)   -> TErequires (r, go b)
      | TErequires_vfx (r, b) -> TErequires_vfx (r, go b)
      | TElet (n, v, b)     -> TElet (n, v, go b)
      | other -> other
    in go e
  in
  let records_to_new e = map_texpr (function
    | TErecord flds' ->
        (match List.find_opt (fun (_, fs) ->
             List.length fs = List.length flds' &&
             List.for_all (fun (n, _) -> List.mem_assoc n flds') fs
           ) all_record_defs
         with
         | Some (cname, fs) ->
             let vals = List.map (fun (fname, ftp) ->
               annotate_empty_set ftp (List.assoc fname flds')) fs in
             TEcall ({ fn_name = "new " ^ record_class_name decls cname; fn_params = []; fn_return = TTInt }, vals)
         | None -> TErecord flds')
    | other -> other) e
  in
  let fix_map_const e = map_texpr (function
    | TEcall ({ fn_name = "map.const"; fn_return = TTMap (k, v); _ }, _) ->
        TEvar { v_name = Printf.sprintf "new Map[%s, %s]()" (local_tp k) (local_tp v); v_tp = TTBool }
    | other -> other) e
  in
  let subst_bare_const e = map_texpr (function
    | TEcall ({ fn_name = c; _ }, []) when List.mem_assoc c const_field_map ->
        TEvar { v_name = "this." ^ List.assoc c const_field_map; v_tp = TTBool }
    | TEvar { v_name = c; _ } when List.mem_assoc c const_field_map ->
        TEvar { v_name = "this." ^ List.assoc c const_field_map; v_tp = TTBool }
    | other -> other) e
  in

  let proof_trait = if is_generic then "CmRDTProof1" else "CmRDTProof" in
  fprintf ppf "import org.verifx.practical.crdts.CmRDT\n";
  fprintf ppf "import org.verifx.practical.crdts.%s\n" proof_trait;
  (match compose_class_name with
   | Some ccls when ccls <> class_name ->
       fprintf ppf "import org.verifx.practical.exercises.%s\n" ccls
   | _ -> ());
  List.iter (fun (rname, _, _) ->
    fprintf ppf "import org.verifx.practical.exercises.%s\n" (record_class_name decls rname))
    behavioral_records;
  fprintf ppf "\n";

  List.iter (fun (name, fields) ->
    let is_this_rec = List.mem name generic_aux_record_names in
    let field_str = String.concat ", "
      (List.map (fun (n, tp) -> Printf.sprintf "%s: %s" n (local_tp tp)) fields)
    in
    fprintf ppf "class %s%s(%s)\n\n" (record_class_name decls name) (if is_this_rec then "[V]" else "") field_str
  ) (List.filter (fun (name, _) -> not (List.exists (fun (rn, _, _) -> rn = name) behavioral_records)) aux_records);

  if msg_ctors <> [] then begin
    let pp_enum_body ppf enum_name ctors =
      fprintf ppf "  enum %s%s {\n" enum_name generic_tag;
      fprintf ppf "    %s\n"
        (String.concat " | "
          (List.map (fun (c, fields) ->
            if fields = [] then Printf.sprintf "%s()" c
            else Printf.sprintf "%s(%s)" c
              (String.concat ", "
                (List.map (fun (n, tp) -> Printf.sprintf "%s: %s" n (local_tp tp)) fields))
          ) ctors));
      fprintf ppf "  }\n"
    in
    fprintf ppf "object Op {\n";
    pp_enum_body ppf op_type_name op_ctors;
    if has_source then begin
      fprintf ppf "\n";
      pp_enum_body ppf msg_type_name msg_ctors;
    end;
    fprintf ppf "}\n\n"
  end;

  let display_payload_fields =
    match set_field_pair, compose_field_name, compose_class_name with
    | Some (n1, n2, elem_tp), Some cname, Some ccls ->
        List.filter_map (fun (n, tp) ->
          if n = n1 then Some (cname, `Compose (ccls, elem_tp))
          else if n = n2 then None
          else Some (n, `Plain tp)) payload_fields
    | _ -> List.map (fun (n, tp) -> (n, `Plain tp)) payload_fields
  in
  let pp_field_ty _n = function
    | `Compose (ccls, elem_tp) -> Printf.sprintf "%s[%s]" ccls (local_tp elem_tp)
    | `Plain tp -> local_tp tp
  in
  let ctor_args = String.concat ", "
    (List.map (fun (n, k) -> Printf.sprintf "%s: %s" n (pp_field_ty n k)) display_payload_fields)
  in
  fprintf ppf "class %s%s(%s) extends CmRDT[%s%s, %s%s, %s%s] {\n"
    class_name generic_tag ctor_args
    op_type_name generic_tag msg_type_name generic_tag class_name generic_tag;

  let trait_override_names = ["enabledSrc"; "enabledDown"; "compatibleS"; "reachable"; "compatible"] in
  let has_explicit_effect =
    List.exists (function TDval ({ fn_name = "effect"; _ }, _, _, _) -> true | _ -> false) decls
  in
  List.iter (function
    | TDval (fn, _, _, _) when List.mem fn.fn_name body_less_consts -> ()
    | TDval (fn, _, _, _) when List.mem fn.fn_name record_method_names -> ()
    | TDval ({ fn_name = "execute"; _ }, _, _, _) when has_explicit_effect -> ()
    | TDval (fn, body, _, variant_opt)
      when fn.fn_name <> "compare" && fn.fn_name <> name_equals && fn.fn_name <> "equals_extra"
        && fn.fn_name <> name_init_state ->
        let self_name = self_param_name fn in
        let other_name = other_param_name fn in
        let const_positions = match List.assoc_opt fn.fn_name const_sourced_positions with
          | Some ps -> ps | None -> []
        in
        let const_param_subst = List.filter_map (fun (i, field) ->
          match List.nth_opt fn.fn_params i with
          | Some p -> Some (p.v_name, field)
          | None -> None) const_positions
        in
        let subst_const_params e = map_texpr (function
          | TEvar v ->
              (match List.assoc_opt v.v_name const_param_subst with
               | Some field -> TEvar { v with v_name = "this." ^ field }
               | None -> TEvar v)
          | other -> other) e
        in
        let body = strip_fuel_guard fn.fn_name body in
        let body' = match self_name with
          | Some n -> rewrite_name n "this" body
          | None -> body
        in
        let body' = match other_name with
          | Some n -> rewrite_name n "that" body'
          | None -> body'
        in
        let body' = subst_const_params body' in
        let body' = subst_bare_const body' in
        let body' = rewrite_record_method_calls decls body' in
        let body' = add_this_prefix body' in
        let body' = resolve_quantifier_types (forall_to_collection (records_to_new (hoist_record_ifs_vfx (compose_added_removed (fix_map_const (new_ctor_prefix body')))))) in
        let req_opt, body' = match body' with
          | TErequires (req, b) -> (Some req, b)
          | TErequires_vfx (req, b) -> (Some req, b)
          | other -> (None, other)
        in
        let fuel_param_name = match List.assoc_opt fn.fn_name fuel_elim_positions with
          | Some i -> (match List.nth_opt fn.fn_params i with Some p -> Some p.v_name | None -> None)
          | None -> None
        in
        let const_param_names = List.map fst const_param_subst in
        let args_to_print = List.filter_map (fun (v : var) ->
          if Some v.v_name = self_name then None
          else if List.mem v.v_name const_param_names then None
          else if Some v.v_name = fuel_param_name then None
          else if Some v.v_name = other_name then Some ("that", class_name ^ generic_tag)
          else if fn.fn_name = "enabledDown" && local_tp v.v_tp = op_type_name then Some (v.v_name, msg_type_name)
          else Some (v.v_name, local_tp v.v_tp)
        ) fn.fn_params in
        let pp_arg ppf (n, t_str) = fprintf ppf "%s: %s" n t_str in
        let is_rec = variant_opt <> None || collect_calls fn.fn_name body [] <> [] in
        let override_kw = if List.mem fn.fn_name trait_override_names then "override " else "" in
        let vfx_fn_name = if fn.fn_name = "execute" then "effect" else fn.fn_name in
        let ret_ty =
          if fn.fn_name = "enabledDown" then "Boolean"
          else local_tp fn.fn_return
        in
        (match req_opt with
         | Some req ->
             let req_text = render_indented_vfx ~indent:"    " req in
             fprintf ppf "  pre %s(%a) {\n    %s\n  }\n\n"
               vfx_fn_name
               (pp_print_list ~pp_sep:pp_sep_comma pp_arg) args_to_print
               req_text
         | None -> ());
        if is_rec then fprintf ppf "  @recursive\n";
        let is_match = req_opt = None && (match body' with TEmatch _ -> true | _ -> false) in
        if is_match then
          let body_text = render_indented_vfx ~indent:"  " body' in
          fprintf ppf "  %s%sdef %s(%a): %s = %s\n\n"
            override_kw (if is_rec then "private " else "") vfx_fn_name
            (pp_print_list ~pp_sep:pp_sep_comma pp_arg) args_to_print
            ret_ty
            body_text
        else
          let body_text = render_indented_vfx ~indent:"    " body' in
          fprintf ppf "  %s%sdef %s(%a): %s = {\n    %s\n  }\n\n"
            override_kw (if is_rec then "private " else "") vfx_fn_name
            (pp_print_list ~pp_sep:pp_sep_comma pp_arg) args_to_print
            ret_ty
            body_text
    | _ -> ()
  ) decls;

  (match List.find_opt (function TDval ({ fn_name = "equals"; _ }, _, _, _) -> true | _ -> false) decls,
         List.find_opt (function TDval ({ fn_name = "compare"; _ }, _, _, _) -> true | _ -> false) decls
   with
   | Some _, Some (TDval (cfn, cbody, _, _)) ->
       let rec mentions sn on fname e = match e with
         | TEvar v -> v.v_name = sn ^ "." ^ fname || v.v_name = on ^ "." ^ fname
         | TEcall (_, args) -> List.exists (mentions sn on fname) args
         | TEfield (e, _) -> mentions sn on fname e
         | TEbinop (_, l, r) -> mentions sn on fname l || mentions sn on fname r
         | TEnot e | TEneg e -> mentions sn on fname e
         | TEif (c, e1, e2) -> mentions sn on fname c || mentions sn on fname e1 || mentions sn on fname e2
         | TErecord flds -> List.exists (fun (_, v) -> mentions sn on fname v) flds
         | TEmatch (es, cases) ->
             List.exists (mentions sn on fname) es || List.exists (fun (_, b) -> mentions sn on fname b) cases
         | TErequires (r, b) -> mentions sn on fname r || mentions sn on fname b
         | TErequires_vfx (r, b) -> mentions sn on fname r || mentions sn on fname b
         | _ -> false
       in
       let equals_fields =
         match self_param_name cfn, other_param_name cfn with
         | Some sn, Some on ->
             let plain_fields = List.filter_map (fun (n, _) ->
               match set_field_pair with
               | Some (n1, n2, _) when n = n1 || n = n2 -> None
               | _ -> if mentions sn on n cbody then Some (n, false) else None
             ) payload_fields in
             let compose_field =
               match set_field_pair, compose_field_name with
               | Some (n1, n2, _), Some cf when mentions sn on n1 cbody || mentions sn on n2 cbody ->
                   [(cf, true)]
               | _ -> []
             in
             let extra_fields =
               match List.find_opt (function TDval ({ fn_name = "equals_extra"; _ }, _, _, _) -> true | _ -> false) decls with
               | Some (TDval (efn, ebody, _, _)) ->
                   (match self_param_name efn, other_param_name efn with
                    | Some esn, Some eon ->
                        List.filter_map (fun (n, _) ->
                          if List.mem_assoc n plain_fields || List.mem_assoc n compose_field then None
                          else if mentions esn eon n ebody then Some (n, false) else None
                        ) payload_fields
                    | _ -> [])
               | _ -> []
             in
             compose_field @ plain_fields @ extra_fields
         | _ -> []
       in
       if equals_fields <> [] then begin
         fprintf ppf "  override def equals(that: %s%s): Boolean = {\n    " class_name generic_tag;
         fprintf ppf "%a"
           (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " &&\n    ") (fun ppf (n, is_compose) ->
              if is_compose then fprintf ppf "this.%s.equals(that.%s)" n n
              else fprintf ppf "this.%s == that.%s" n n))
           equals_fields;
         fprintf ppf "\n  }\n\n"
       end
   | _ -> ());

  fprintf ppf "}\n\n";
  fprintf ppf "object %s extends %s[%s, %s, %s]\n"
    class_name proof_trait op_type_name msg_type_name class_name

let is_cvrdt_sig sig_name = sig_name = "CvRDT"
let is_cmrdt_sig sig_name = sig_name = "CmRDT"

let pp_vfx_module ppf (mod_name, sig_name, intfs, decls, all_modules) =
  if is_cvrdt_sig sig_name && map_poly_types decls <> None then
    pp_vfx_map_poly_module ppf (mod_name, intfs, decls)
  else if is_cvrdt_sig sig_name then begin
    match get_set_elem_type decls with
    | Some elem_tp when is_pure_set_payload decls ->
        pp_vfx_set_module ppf (mod_name, sig_name, elem_tp, decls)
    | _ -> pp_vfx_cvrdt_module ppf (mod_name, decls, all_modules)
  end else if is_cmrdt_sig sig_name then begin
    match get_set_elem_type decls with
    | Some elem_tp when is_pure_set_payload decls ->
        pp_vfx_cmrdt_set_module ppf (mod_name, sig_name, elem_tp, decls)
    | Some _ -> pp_vfx_cmrdt_record_module ppf (mod_name, sig_name, decls, all_modules)
    | None   ->
        let payload_is_record = List.exists (function
          | TDtype (n, TTRecord _, _, _) when n = name_payload -> true
          | _ -> false) decls
        in
        if payload_is_record
        then pp_vfx_cmrdt_record_module ppf (mod_name, sig_name, decls, all_modules)
        else pp_vfx_cmrdt_module ppf (mod_name, decls)
  end

let vfx_module_files_of_tfile tfile =
  let exercises_path = "verifx/src/main/verifx/org/verifx/practical/exercises/" in
  let all_modules = List.filter_map (function
    | TDefModule (n, _, _, d) -> Some (n, d)
    | TDefInterface _ -> None) tfile
  in
  List.concat_map (function
    | TDefModule (mod_name, sig_name, intfs, decls) ->
        let class_name = mod_name in
        let should_emit = is_cvrdt_sig sig_name || is_cmrdt_sig sig_name in
        if not should_emit then []
        else
          let main_file =
            (exercises_path ^ class_name ^ ".vfx",
             fun fmt -> pp_vfx_module fmt (mod_name, sig_name, intfs, decls, all_modules))
          in
          let record_files =
            if is_cmrdt_sig sig_name then
              List.map (fun (rname, fields, names) ->
                let rclass = record_class_name decls rname in
                (exercises_path ^ rclass ^ ".vfx",
                 fun fmt -> pp_vfx_record_class fmt decls (rname, fields, resolve_class_methods decls rname names)))
                (class_directive_records decls)
            else []
          in
          record_files @ [main_file]
    | TDefInterface _ -> []) tfile

let vfx_files_of_tfile tfile =
  let crdts_path = "verifx/src/main/verifx/org/verifx/practical/crdts/" in
  
  let intf_files = List.filter_map (function
    | TDefInterface (name, proof, intfs) ->
        if is_cvrdt_interface intfs then
          Some [
            (crdts_path ^ name ^ ".vfx",       fun fmt -> pp_vfx_cvrdt fmt (name, intfs));
            (crdts_path ^ name ^ "Proof.vfx",  fun fmt -> pp_vfx_cvrdt_proof fmt (name, proof, intfs));
            (crdts_path ^ name ^ "Proof1.vfx", fun fmt -> pp_vfx_cvrdt_proof1 fmt (name, proof, intfs));
            (crdts_path ^ name ^ "Proof2.vfx", fun fmt -> pp_vfx_cvrdt_proof2 fmt (name, proof, intfs));
          ]
        else
          Some [
            (crdts_path ^ name ^ ".vfx",       fun fmt -> pp_vfx_cmrdt fmt (name, intfs));
            (crdts_path ^ name ^ "Proof.vfx",  fun fmt -> pp_vfx_cmrdt_proof fmt (name, proof, intfs));
            (crdts_path ^ name ^ "Proof1.vfx", fun fmt -> pp_vfx_cmrdt_proof1 fmt (name, proof, intfs));
            (crdts_path ^ name ^ "Proof2.vfx", fun fmt -> pp_vfx_cmrdt_proof2 fmt (name, proof, intfs));
          ]
    | TDefModule _ -> None) tfile
  |> List.flatten
  in
  let module_files = vfx_module_files_of_tfile tfile in
  intf_files @ module_files
