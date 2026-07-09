open Ast
module H = Hashtbl

let debug = ref false
let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of Ast.location * string

let error ?(loc = dummy_loc) f =
  Format.kasprintf (fun s -> raise (Error (loc, s))) ("@[" ^^ f ^^ "@]")

type var_env    = (string, var) H.t
type fn_env     = (string, fn) H.t
type record_env = (string, (string * ttp) list) H.t
type type_env   = (string, ttp) H.t

let rec resolve_type (t : Ast.tp) : Ast.ttp =
  match t with
  | Tcst { id = "integer"; _ } -> TTInt
  | Tcst { id = "boolean"; _ } -> TTBool
  | Tcst { id = name; _ }      -> TTModuleRecord name
  | Tmap (t1, t2) -> TTMap (resolve_type t1, resolve_type t2)
  | Tset elem     -> TTSet (resolve_type elem)
  | Trecord fields -> 
      let tfields = List.map (fun (id, tp) -> (id.id, resolve_type tp)) fields in
      TTRecord tfields
  | Taccess path -> 
      let full_path = String.concat "." (List.map (fun id -> id.id) path) in
      TTModuleRecord full_path
  | Tinvariant inv ->
      let string_path = List.map (fun id -> id.id) inv in
      TTInvariant string_path
  | Tvariant variants ->
      TTVariant ("", List.map (fun id -> id.id) variants)
  | Tattribute (core, _attr) ->
      resolve_type core

let rec expand_type (types : type_env) (tp : ttp) : ttp =
  match tp with
  | TTModuleRecord name ->
      begin try
        expand_type types (H.find types name)
        with Not_found -> tp
      end
  | TTMap (k, v) -> TTMap (expand_type types k, expand_type types v)
  | TTSet elem   -> TTSet (expand_type types elem)
  | TTRecord fields -> TTRecord (List.map (fun (n, t) -> (n, expand_type types t)) fields)
  | TTVariant _ -> tp
  | TTAbstract _ -> tp
  | _ -> tp

let rec expr (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (ex : Ast.expr) : Ast.texpr * Ast.ttp =
  match ex with
  | Ecst (Cint c) -> (TEcst (Cint c), TTInt)
  | Ecst (Cbool b) -> (TEcst (Cbool b), TTBool)
  | Ecst _ -> error "Const not supported."
  | Eaccess path -> begin
      let first_ident = List.hd path in
      let full_path = String.concat "." (List.map (fun id -> id.id) path) in
      try
        let v = H.find ctx first_ident.id in
        if List.length path = 1 then
          (TEvar v, v.v_tp)
        else
          begin match v.v_tp with
          | TTModuleRecord type_name ->
              begin try
                let fields = H.find records type_name in
                let field_ident = List.nth path 1 in
                begin try
                  let field_type = List.assoc field_ident.id fields in
                  (TEvar { v_name = full_path; v_tp = field_type }, field_type)
                with Not_found ->
                  error ~loc:field_ident.loc "Field '%s' does not exist in '%s'." field_ident.id type_name
                end
              with Not_found ->
                error ~loc:first_ident.loc "Definition '%s' does not exist." type_name
              end
          | _ -> error ~loc:first_ident.loc "Variable '%s' is not a record." first_ident.id
          end
      with Not_found ->
        begin match H.find_opt fns full_path with
        | Some f ->
            (TEcall (f, []), f.fn_return)
        | None ->
            error ~loc:first_ident.loc "Undeclared variable: '%s'." first_ident.id
        end
    end
  | Ebinop (b, ex1, ex2) ->
    let (tex1, type1) = expr ctx fns records types ex1 in
    let (tex2, type2) = expr ctx fns records types ex2 in
    begin match b with
      | Badd | Bsub | Bmul | Bdiv ->
        if expand_type types type1 = TTInt && expand_type types type2 = TTInt then (TEbinop (b, tex1, tex2), TTInt)
        else error "Expected integer type variables for mathematical operation."
      | Beq | Bneq ->
        if expand_type types type1 = expand_type types type2 then (TEbinop (b, tex1, tex2), TTBool)
        else error "Type mismatch for comparison."
      | Blt | Ble | Bgt | Bge ->
        if expand_type types type1 = TTInt && expand_type types type2 = TTInt then (TEbinop (b, tex1, tex2), TTBool)
        else error "Expected integer type variables for logical comparisons."
      | Band | Bor ->
        if expand_type types type1 = TTBool && expand_type types type2 = TTBool then (TEbinop (b, tex1, tex2), TTBool)
        else error "Expected boolean type variables for this logical operations."
    end
  | Ecall (f, args) ->
    let func_name = String.concat "." (List.map (fun id -> id.id) f) in
    let last_ident = List.hd (List.rev f) in
    begin try
      let f = H.find fns func_name in
      if List.length args <> List.length f.fn_params then
        error ~loc:last_ident.loc "Incorrect number of arguments for function '%s'." func_name
      else
        let compatible_types t1 t2 =
          expand_type types t1 = expand_type types t2
        in
        let targs = List.map2 (fun arg param ->
          let (targ_expr, targ_type) = expr ctx fns records types arg in
          if not (compatible_types targ_type param.v_tp) then
            error ~loc: last_ident.loc "Argument type error for function '%s'." func_name
          else targ_expr
        ) args f.fn_params in
        (TEcall (f, targs), f.fn_return)
    with Not_found -> error ~loc:last_ident.loc "Undeclared function: '%s'." func_name
    end
  | Erecord fields ->
      let field_names = List.map (fun (id, _) -> id.id) fields in
      let matching_record = H.fold (fun rec_name rec_fields acc ->
        match acc with
        | Some _ -> acc
        | None ->
            let rec_field_names = List.map fst rec_fields in
            if List.length field_names = List.length rec_field_names &&
               List.for_all (fun f -> List.mem f rec_field_names) field_names
            then Some (rec_name, rec_fields)
            else None
      ) records None in
      begin match matching_record with
      | Some (rec_name, expected_fields) ->
          let tfields = List.map (fun (id, ex) ->
            let (tex, ttype) = expr ctx fns records types ex in
            begin try
              let expected_type = List.assoc id.id expected_fields in
              if expand_type types ttype <> expand_type types expected_type then
                error ~loc:id.loc "Incorrect type for '%s'." id.id;
              (id.id, tex)
            with Not_found ->
              error ~loc:id.loc "Field '%s' not part of record." id.id
            end
          ) fields in
          (TErecord tfields, TTModuleRecord rec_name)
      | None ->
          begin match fields with
          | [(id, ex)] when id.id = "payload" ->
              let (tex, ttype) = expr ctx fns records types ex in
              let declared_payload = try H.find types "payload"
                                     with Not_found -> ttype in
              let compatible t1 t2 =
                let e1 = expand_type types t1 and e2 = expand_type types t2 in
                match e1, e2 with
                | TTSet _,     TTSet _     -> true
                | TTAbstract _, _          -> true
                | _,           TTAbstract _ -> true
                | _ -> e1 = e2
              in
              if not (compatible ttype declared_payload) then
                error ~loc:id.loc "Incorrect type for '%s'." id.id;
              (TErecord [(id.id, tex)], TTModuleRecord "payload")
          | _ ->
              error "No matching record type found for this record expression."
          end
      end
  | Ematch (main_ex, cases) ->
      let (tmain_ex, main_type) = expr ctx fns records types main_ex in
      let expanded_main_type = expand_type types main_type in
      begin match expanded_main_type with
      | TTVariant (_, valid) ->
          List.iter (fun (id, _) ->
            if not (List.mem id.id valid) then
              error ~loc:id.loc "Constructor '%s' does not belong to the matched type." id.id
          ) cases
      | _ ->
          error "Match expression requires a variant type."
      end;
      let _first_case_ident, first_case_expr = List.hd cases in
      let (_tfirst_expr, expected_return_type) = expr ctx fns records types first_case_expr in
      let tcases = List.map (fun (id, branch_expr) ->
        let (tbranch_expr, branch_type) = expr ctx fns records types branch_expr in
        if expand_type types branch_type <> expand_type types expected_return_type then
          error ~loc:id.loc "Type mismatch on match."
        else
          (id.id, tbranch_expr)
      ) cases in
      (TEmatch (tmain_ex, tcases), expected_return_type)

let extract_vfx_attr (tp : Ast.tp) : string option =
  match tp with
  | Tattribute (_, attr) -> Some attr
  | _ -> None

let mod_decl (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (d : Ast.modl) : Ast.tmodl =
  match d with
  | Dtype (id, tp, inv_opt) ->
      let vfx_attr = extract_vfx_attr tp in
      let ttype = resolve_type tp in
      let ttype = match tp, ttype with
        | Tcst self_id, TTModuleRecord name when self_id.id = id.id && name = id.id ->
            TTAbstract id.id
        | _ -> ttype
      in
      let ttype = match ttype with
        | TTVariant (_, ctors) -> TTVariant (id.id, ctors)
        | other -> other
      in
      H.replace types id.id ttype;
      begin match ttype with
      | TTRecord fields -> H.add records id.id fields
      | TTVariant (type_name, ctors) ->
          List.iter (fun ctor ->
            H.add ctx ctor { v_name = ctor; v_tp = TTModuleRecord type_name }
          ) ctors
      | _ -> ()
      end;
      let tinv = match inv_opt with
        | None  -> None
        | Some (inv_id, inv_params, inv_ex) ->
          let inv_ctx = H.copy ctx in
          let tparams = List.map (fun (param_id, param_tp) ->
            let v = { v_name = param_id.id; v_tp = resolve_type param_tp } in
            H.replace inv_ctx param_id.id v;
            v
          ) inv_params in
          let (tex, expr_type) = expr inv_ctx fns records types inv_ex in
          if expr_type <> TTBool then
            error ~loc:id.loc "Invariant '%s' result not a boolean." inv_id.id;
          let inv_fn = { fn_name = inv_id.id; fn_params = tparams; fn_return = TTBool } in
          Some (inv_fn, tex)
      in
      TDtype (id.id, ttype, tinv, vfx_attr)
  | Dval (id, params, tp, ex, vfx_attr) ->
      let local_ctx = H.copy ctx in
      let tparams = List.map (fun (p_id, p_tp) ->
        let v = { v_name = p_id.id; v_tp = resolve_type p_tp } in
        H.replace local_ctx p_id.id v;
        v
      ) params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = resolve_type tp } in
      H.add fns id.id f;
      let (tex, _) = expr local_ctx fns records types ex in
      let vfx_param = match vfx_attr with
        | None -> None
        | Some (attr_id, attr_tp) -> Some (attr_id.id, resolve_type attr_tp)
      in
      TDval (f, tex, vfx_param)

let builtin_fns : (string * fn) list =
  let int_int_int name = (name, {
    fn_name = name;
    fn_params = [{ v_name = "a"; v_tp = TTInt }; { v_name = "b"; v_tp = TTInt }];
    fn_return = TTInt;
  }) in
  [ int_int_int "max"; int_int_int "min" ]

let file ?debug:(b = false) (p : Ast.file) : Ast.tfile =
  debug := b;
  let fns = H.create 16 in
  List.iter (fun (name, f) -> H.add fns name f) builtin_fns;
  let ctx = H.create 16 in
  let records = H.create 16 in
  let types = H.create 16 in
  let interfaces = H.create 16 in
  let global_fns   = H.create 16 in
  List.iter (fun (name, f) -> H.add global_fns name f) builtin_fns;
  let global_types   = H.create 16 in
  let global_records = H.create 16 in

  let rec process_defs defs mdls =
    match defs with
    | [] -> List.rev mdls
    | DefInterface (name, proof, lines) :: rest ->
        H.add interfaces name.id lines;
        let tdef = TDefInterface (name.id, proof, lines) in
        process_defs rest (tdef :: mdls)
    | DefModule (name, _params, interface, lines) :: rest ->
        H.clear ctx;
        H.clear fns;
        List.iter (fun (name, f) -> H.replace fns name f) builtin_fns;
        H.iter (fun k v -> H.replace fns k v) global_fns;
        H.clear records;
        H.iter (fun k v -> H.replace records k v) global_records;
        H.clear types;
        H.iter (fun k v -> H.replace types k v) global_types;
        let set_elem_opt = List.fold_left (fun acc d -> match d with
          | Dtype (_, Tset elem_tp, _) -> Some (resolve_type elem_tp)
          | _ -> acc) None lines
        in
        (match set_elem_opt with
         | Some elem_tp ->
             let set_tp = TTSet elem_tp in
             let set_fns = [
               ("set.empty", {
                 fn_name   = "set.empty";
                 fn_params = [];
                 fn_return = set_tp;
               });
               ("set.add", {
                 fn_name   = "set.add";
                 fn_params = [{ v_name = "v"; v_tp = elem_tp };
                              { v_name = "s"; v_tp = set_tp }];
                 fn_return = set_tp;
               });
               ("set.union", {
                 fn_name   = "set.union";
                 fn_params = [{ v_name = "a"; v_tp = set_tp };
                              { v_name = "b"; v_tp = set_tp }];
                 fn_return = set_tp;
               });
               ("set.contains", {
                 fn_name   = "set.contains";
                 fn_params = [{ v_name = "v"; v_tp = elem_tp };
                              { v_name = "s"; v_tp = set_tp }];
                 fn_return = TTBool;
               });
               ("set.subset", {
                 fn_name   = "set.subset";
                 fn_params = [{ v_name = "a"; v_tp = set_tp };
                              { v_name = "b"; v_tp = set_tp }];
                 fn_return = TTBool;
               });
             ] in
             List.iter (fun (n, f) -> H.replace fns n f) set_fns
         | None -> ());
        let tlines = List.map (mod_decl ctx fns records types) lines in
        H.iter (fun k v ->
          let module_fn = name.id ^ "." ^ k in
          H.replace global_fns module_fn
            { fn_name = module_fn;
              fn_return = expand_type types v.fn_return;
              fn_params = List.map (fun p ->
                { p with v_tp = expand_type types p.v_tp }) v.fn_params }
        ) fns;
        H.iter (fun k v ->
          H.replace global_types (name.id ^ "." ^ k) (expand_type types v)) types;
        H.iter (fun k v ->
          H.replace global_records (name.id ^ "." ^ k) v) records;
        if H.mem fns "init_state" then begin
          let payload_tp = try expand_type types (H.find types "payload")
                           with Not_found -> TTInt in
          let ext_payload_tp = TTModuleRecord (name.id ^ ".payload") in
          H.replace global_fns (name.id ^ ".get_payload") {
            fn_name = name.id ^ ".get_payload";
            fn_params = [{ v_name = "a"; v_tp = ext_payload_tp }];
            fn_return = payload_tp;
          };
          H.replace global_fns (name.id ^ ".create") {
            fn_name = name.id ^ ".create";
            fn_params = [];
            fn_return = ext_payload_tp;
          }
        end;

        begin try
          let expected_lines = H.find interfaces interface.id in
          List.iter (fun req ->
            match req with
            | Itype expected_id ->
              let found = List.exists (function
                | TDtype (tname, _, _, _) -> tname = expected_id.id
                | _ -> false) tlines in
              if not found then
                error ~loc:name.loc "Module '%s' missing type '%s' present in interface '%s'." name.id expected_id.id interface.id
            | Ifunc (expected_id, expected_params, expected_tp) ->
              begin try
                let f = H.find fns expected_id.id in
                let expected_return = resolve_type expected_tp in
                if f.fn_return <> expected_return then
                  error ~loc:expected_id.loc "Function '%s' return type does not respect the interface's." expected_id.id;
                if List.length f.fn_params <> List.length expected_params then
                  error ~loc:expected_id.loc "Function '%s' has wrong number of arguments." expected_id.id;
              with Not_found ->
                error ~loc:name.loc "Module '%s' missing function '%s'." name.id expected_id.id
              end
          | Iaxiom _ -> ()
          ) expected_lines
        with Not_found -> error ~loc:interface.loc "Interface '%s' does not exist." interface.id
        end;

        let tmodl = TDefModule (name.id, interface.id, (H.find interfaces interface.id), tlines) in
        process_defs rest (tmodl :: mdls)
  in
  process_defs p []
