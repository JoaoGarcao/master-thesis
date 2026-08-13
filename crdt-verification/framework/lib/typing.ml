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
  | Tmap (k, v) -> TTMap (resolve_type k, resolve_type v)
  | Tset v -> TTSet (resolve_type v)
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
  | TvariantArgs ctors ->
      TTVariantArgs ("", List.map (fun (id, tp) -> (id.id, resolve_type tp)) ctors)
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
  | TTSet v -> TTSet (expand_type types v)
  | TTRecord fields -> TTRecord (List.map (fun (n, t) -> (n, expand_type types t)) fields)
  | TTVariantArgs (name, ctors) ->
      TTVariantArgs (name, List.map (fun (c, t) -> (c, expand_type types t)) ctors)
  | _ -> tp

let lookup_field (records : record_env) (types : type_env) (base_tp : ttp) (field_id : Ast.ident) : ttp =
  let fields = match expand_type types base_tp with
    | TTRecord fs -> fs
    | TTModuleRecord record_name ->
        begin try H.find records record_name
        with Not_found -> error ~loc:field_id.loc "Definition '%s' does not exist." record_name
        end
    | _ -> error ~loc:field_id.loc "Cannot access field '%s': not a record." field_id.id
  in
  try List.assoc field_id.id fields
  with Not_found -> error ~loc:field_id.loc "Field '%s' does not exist." field_id.id

let type_params (ctx : var_env) params =
  let local_ctx = H.copy ctx in
  let tparams = List.map (fun (p_id, p_tp) ->
    let v = { v_name = p_id.id; v_tp = resolve_type p_tp } in
    H.replace local_ctx p_id.id v;
    v
  ) params in
  (local_ctx, tparams)

let resolve_variant (owner_id : Ast.ident) (tparams : var list) variant_opt =
  match variant_opt with
  | None -> None
  | Some idents ->
      Some (List.map (fun v_id ->
        match List.find_opt (fun p -> p.v_name = v_id.id) tparams with
        | Some p when p.v_tp = TTInt -> p.v_name
        | Some _ -> error ~loc:v_id.loc "Variant measure '%s' must be an integer parameter." v_id.id
        | None -> error ~loc:v_id.loc "Variant measure '%s' is not a parameter of '%s'." v_id.id owner_id.id
      ) idents)

let rec expr (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (ex : Ast.expr) : Ast.texpr * Ast.ttp =
  match ex with
  | Ecst (Cint c) -> (TEcst (Cint c), TTInt)
  | Ecst (Cbool b) -> (TEcst (Cbool b), TTBool)
  | Ecst Cnone -> (TEcst Cnone, TTBool)
  | Ecst _ -> error "Const not supported."
  | Eaccess path -> begin
      let first_ident = List.hd path in
      try
        let v = H.find ctx first_ident.id in
        if List.length path = 1 then
          (TEvar v, v.v_tp)
        else
          let rec walk cur_tp cur_name rest_path =
            match rest_path with
            | [] -> (TEvar { v_name = cur_name; v_tp = cur_tp }, cur_tp)
            | field_ident :: tl ->
                let field_type = lookup_field records types cur_tp field_ident in
                walk field_type (cur_name ^ "." ^ field_ident.id) tl
          in
          walk v.v_tp v.v_name (List.tl path)
      with Not_found ->
        let full_path = String.concat "." (List.map (fun id -> id.id) path) in
        begin match H.find_opt fns full_path with
        | Some f ->
            (TEcall (f, []), f.fn_return)
        | None ->
            error ~loc:first_ident.loc "Undeclared variable or function: '%s'." first_ident.id
        end
    end
  | Efield (base_ex, field_ident) ->
      let (tbase, base_tp) = expr ctx fns records types base_ex in
      let field_type = lookup_field records types base_tp field_ident in
      (TEfield (tbase, field_ident.id), field_type)
  | Enot e ->
      let (te, tp) = expr ctx fns records types e in
      if expand_type types tp <> TTBool then
        error "Expected boolean expression after '!'.";
      (TEnot te, TTBool)
  | Erequires (req, body) ->
      let (treq, req_tp) = expr ctx fns records types req in
      if expand_type types req_tp <> TTBool then
        error "Requires clause must be a boolean expression.";
      let (tbody, body_tp) = expr ctx fns records types body in
      (TErequires (treq, tbody), body_tp)
  | Erequires_vfx (req, body) ->
      let (treq, req_tp) = expr ctx fns records types req in
      if expand_type types req_tp <> TTBool then
        error "Requires clause must be a boolean expression.";
      let (tbody, body_tp) = expr ctx fns records types body in
      (TErequires_vfx (treq, tbody), body_tp)
  | Eforall (vars, body) | Eexists (vars, body) ->
      let (local_ctx, tvars) = type_params ctx vars in
      let (tbody, body_tp) = expr local_ctx fns records types body in
      if expand_type types body_tp <> TTBool then
        error "Result of 'forall'/'exists' must be a boolean expression.";
      (match ex with
       | Eforall _ -> (TEforall (tvars, tbody), TTBool)
       | _         -> (TEexists (tvars, tbody), TTBool))
  | Eneg e ->
      let (te, tp) = expr ctx fns records types e in
      if expand_type types tp <> TTInt then
        error "Expected integer expression after unary '-'.";
      (TEneg te, TTInt)
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
            error ~loc: last_ident.loc "Argument type mismatch for function '%s'." func_name
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
                | TTSet _, TTSet _ | TTAbstract _, _ | _, TTAbstract _ -> true
                | _ -> e1 = e2
              in
              if not (compatible ttype declared_payload) then
                error ~loc:id.loc "Incorrect type for '%s'." id.id;
              (TErecord [(id.id, tex)], TTModuleRecord "payload")
          | _ ->
              error "No matching record type found for this record expression."
          end
      end
  | Eif (c, e1, e2) ->
      let (tc, c_type) = expr ctx fns records types c in
      if expand_type types c_type <> TTBool then
        error "Expected boolean expression in 'if' condition.";
      let (te1, type1) = expr ctx fns records types e1 in
      let (te2, type2) = expr ctx fns records types e2 in
      if expand_type types type1 <> expand_type types type2 then
        error "Type mismatch between 'then' and 'else' branches."
      else
        (TEif (tc, te1, te2), type1)
  | Ematch (main_exs, cases) ->
      let typed_exprs = List.map (expr ctx fns records types) main_exs in
      let n = List.length typed_exprs in
      let rec unwrap_to_variant tp = match tp with
        | TTModuleRecord name ->
            (try unwrap_to_variant (H.find types name) with Not_found -> tp)
        | _ -> tp
      in
      let exprs_info = List.map (fun (_, tp) ->
        match unwrap_to_variant tp with
        | TTVariant (_, valid)     -> `Enum valid
        | TTVariantArgs (_, ctors) -> `Args ctors
        | _ -> error "Match expression requires a variant type."
      ) typed_exprs in
      let field_types_of arg_tp = match arg_tp with
        | TTRecord fields -> List.map snd fields
        | other           -> [other]
      in
      let check_pattern pattern =
        if List.length pattern <> n then
          error "Wrong number of patterns in match case (expected %d)." n;
        List.map2 (fun (ctor_id, vars) info ->
          match info with
          | `Enum valid ->
              if not (List.mem ctor_id.id valid) then
                error ~loc:ctor_id.loc "'%s' invalid for this match." ctor_id.id;
              if vars <> [] then
                error ~loc:ctor_id.loc "'%s' takes no arguments." ctor_id.id;
              (ctor_id.id, [], [])
          | `Args ctors ->
              begin match List.assoc_opt ctor_id.id ctors with
              | None -> error ~loc:ctor_id.loc "'%s' invalid for this match." ctor_id.id
              | Some arg_tp ->
                  let field_tps = field_types_of arg_tp in
                  if List.length vars <> List.length field_tps then
                    error ~loc:ctor_id.loc
                      "'%s' expects %d argument(s) but %d were given."
                      ctor_id.id (List.length field_tps) (List.length vars);
                  (ctor_id.id, vars, field_tps)
              end
        ) pattern exprs_info
      in
      let bind_case info =
        let branch_ctx = H.copy ctx in
        List.iter (fun (_, vars, field_tps) ->
          List.iter2 (fun var_opt field_tp -> match var_opt with
            | Some v_id -> H.replace branch_ctx v_id.id { v_name = v_id.id; v_tp = field_tp }
            | None -> ()
          ) vars field_tps
        ) info;
        branch_ctx
      in
      (match cases with [] -> error "Match expression has no cases." | _ -> ());
      let (first_pattern, first_body) = List.hd cases in
      let first_ctx = bind_case (check_pattern first_pattern) in
      let (_, expected_return_type) = expr first_ctx fns records types first_body in
      let tcases = List.map (fun (pattern, branch_expr) ->
        let info = check_pattern pattern in
        let branch_ctx = bind_case info in
        let (tbranch_expr, branch_type) = expr branch_ctx fns records types branch_expr in
        if expand_type types branch_type <> expand_type types expected_return_type then
          error "Type mismatch on match.";
        let tpattern = List.map (fun (ctor_name, vars, field_tps) ->
          let tvars = List.map2 (fun var_opt field_tp -> match var_opt with
            | Some v_id -> Some { v_name = v_id.id; v_tp = field_tp }
            | None -> None
          ) vars field_tps in
          (ctor_name, tvars)
        ) info in
        (tpattern, tbranch_expr)
      ) cases in
      (TEmatch (List.map fst typed_exprs, tcases), expected_return_type)

let extract_vfx_attr (tp : Ast.tp) : string option =
  match tp with
  | Tattribute (_, attr) -> Some attr
  | _ -> None

let strip_attr (tp : Ast.tp) : Ast.tp =
  match tp with
  | Tattribute (core, _) -> core
  | t -> t

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
        | TTVariantArgs (_, ctors) -> TTVariantArgs (id.id, ctors)
        | other -> other
      in
      H.replace types id.id ttype;
      begin match ttype with
      | TTRecord fields -> H.add records id.id fields
      | TTVariant (type_name, ctors) ->
          List.iter (fun ctor ->
            H.add ctx ctor { v_name = ctor; v_tp = TTModuleRecord type_name }
          ) ctors
      | TTVariantArgs (type_name, ctors) ->
          List.iter (fun (ctor, arg_tp) ->
            let params = match arg_tp with
              | TTRecord flds -> List.map (fun (n, t) -> { v_name = n; v_tp = t }) flds
              | _ -> [{ v_name = "v"; v_tp = arg_tp }]
            in
            H.add fns ctor {
              fn_name   = ctor;
              fn_params = params;
              fn_return = TTModuleRecord type_name;
            }
          ) ctors
      | _ -> ()
      end;
      let tinv = match inv_opt with
        | None  -> None
        | Some (inv_id, inv_params, inv_ex) ->
          let (inv_ctx, tparams) = type_params ctx inv_params in
          let (tex, expr_type) = expr inv_ctx fns records types inv_ex in
          if expr_type <> TTBool then
            error ~loc:id.loc "Invariant '%s' result not a boolean." inv_id.id;
          let inv_fn = { fn_name = inv_id.id; fn_params = tparams; fn_return = TTBool } in
          Some (inv_fn, tex)
      in
      TDtype (id.id, ttype, tinv, vfx_attr)
  | Dval (id, params, tp, ex, vfx_attr, variant_opt) ->
      let (local_ctx, tparams) = type_params ctx params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = resolve_type tp } in
      H.add fns id.id f;
      let (tex, _) = expr local_ctx fns records types ex in
      let vfx_param = Option.map (fun (attr_id : Ast.ident) -> attr_id.id) vfx_attr in
      let variant = resolve_variant id tparams variant_opt in
      TDval (f, tex, vfx_param, variant)
  | Dlemma (id, params, body, variant_opt, ensures) ->
      let (local_ctx, tparams) = type_params ctx params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = TTBool } in
      H.add fns id.id f;
      let (tbody, _) = expr local_ctx fns records types body in
      let tens = List.map (fun e ->
        let (te, _) = expr local_ctx fns records types e in te) ensures in
      let variant = resolve_variant id tparams variant_opt in
      TDlemma (f, tbody, variant, tens)

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
          | Dtype (_, tp, _) ->
              (match strip_attr tp with
               | Tset elem_tp -> Some (resolve_type elem_tp)
               | Trecord fields ->
                   List.fold_left (fun a (_, ftp) -> match a, strip_attr ftp with
                     | None, Tset elem_tp -> Some (resolve_type elem_tp)
                     | _ -> a) acc fields
               | _ -> acc)
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
               ("set.diff", {
                 fn_name   = "set.diff";
                 fn_params = [{ v_name = "a"; v_tp = set_tp };
                              { v_name = "b"; v_tp = set_tp }];
                 fn_return = set_tp;
               });
               ("set.cardinal", {
                 fn_name   = "set.cardinal";
                 fn_params = [{ v_name = "s"; v_tp = set_tp }];
                 fn_return = TTInt;
               });
             ] in
             List.iter (fun (n, f) -> H.replace fns n f) set_fns
         | None -> ());
        let map_kv_opt = List.fold_left (fun acc d -> match d with
          | Dtype (_, tp, _) ->
              (match strip_attr tp with
               | Tmap (k_tp, v_tp) -> Some (resolve_type k_tp, resolve_type v_tp)
               | Trecord fields ->
                   List.fold_left (fun a (_, ftp) -> match a, strip_attr ftp with
                     | None, Tmap (k_tp, v_tp) -> Some (resolve_type k_tp, resolve_type v_tp)
                     | _ -> a) acc fields
               | _ -> acc)
          | _ -> acc) None lines
        in
        (match map_kv_opt with
         | Some (k_tp, v_tp) ->
             let map_tp = TTMap (k_tp, v_tp) in
             let map_fns = [
               ("map.empty", {
                 fn_name   = "map.empty";
                 fn_params = [];
                 fn_return = map_tp;
               });
               ("map.get", {
                 fn_name   = "map.get";
                 fn_params = [{ v_name = "k"; v_tp = k_tp };
                              { v_name = "m"; v_tp = map_tp }];
                 fn_return = v_tp;
               });
               ("map.set", {
                 fn_name   = "map.set";
                 fn_params = [{ v_name = "k"; v_tp = k_tp };
                              { v_name = "v"; v_tp = v_tp };
                              { v_name = "m"; v_tp = map_tp }];
                 fn_return = map_tp;
               });
               ("map.const", {
                 fn_name   = "map.const";
                 fn_params = [{ v_name = "default"; v_tp = v_tp }];
                 fn_return = map_tp;
               });
               ("map.contains", {
                 fn_name   = "map.contains";
                 fn_params = [{ v_name = "k"; v_tp = k_tp };
                              { v_name = "m"; v_tp = map_tp }];
                 fn_return = TTBool;
               });
             ] in
             List.iter (fun (n, f) -> H.replace fns n f) map_fns
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
