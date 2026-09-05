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

let abstract_axiom_formulas : (string, texpr) H.t = H.create 8

let rec resolve_type (types : type_env) (t : Ast.tp) : Ast.ttp =
  match t with
  | Tcst { id = "integer"; _ } -> TTInt
  | Tcst { id = "boolean"; _ } -> TTBool
  | Tcst { id = name; _ }      ->
      (match H.find_opt types name with
       | Some (TTAbstract _ as abs) -> abs
       | _ -> TTModuleRecord name)
  | Tmap (k, v) -> TTMap (resolve_type types k, resolve_type types v)
  | Tset v -> TTSet (resolve_type types v)
  | Ttuple (t1, t2) -> TTTuple (resolve_type types t1, resolve_type types t2)
  | Trecord fields ->
      let tfields = List.map (fun (id, tp) -> (id.id, resolve_type types tp)) fields in
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
      TTVariantArgs ("", List.map (fun (id, tp) -> (id.id, resolve_type types tp)) ctors)
  | Tattribute (core, _attr) ->
      resolve_type types core

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

let type_params (types : type_env) (ctx : var_env) params =
  let local_ctx = H.copy ctx in
  let tparams = List.map (fun (p_id, p_tp) ->
    let v = { v_name = p_id.id; v_tp = resolve_type types p_tp } in
    H.replace local_ctx p_id.id v;
    v
  ) params in
  (local_ctx, tparams)

let rec expr ?(expected : Ast.ttp option) (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (ex : Ast.expr) : Ast.texpr * Ast.ttp =
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
        if List.mem full_path ["set.union"; "set.diff"; "set.subset"; "set.contains";
                                "map.combine"] then
          (TEcall ({ fn_name = full_path; fn_params = []; fn_return = TTBool }, []), TTBool)
        else
        begin match H.find_opt fns full_path with
        | Some f ->
            (TEcall (f, []), f.fn_return)
        | None ->
            error ~loc:first_ident.loc "Undeclared variable or function: '%s'." first_ident.id
        end
    end
  | Efield (base_ex, field_ident) ->
      let (tbase, base_tp) = expr ctx fns records types base_ex in
      (match expand_type types base_tp, field_ident.id with
       | TTTuple (t1, _), "fst" -> (TEfst tbase, t1)
       | TTTuple (_, t2), "snd" -> (TEsnd tbase, t2)
       | _ ->
           let field_type = lookup_field records types base_tp field_ident in
           (TEfield (tbase, field_ident.id), field_type))
  | Etuple (e1, e2) ->
      let (te1, tp1) = expr ctx fns records types e1 in
      let (te2, tp2) = expr ctx fns records types e2 in
      (TEtuple (te1, te2), TTTuple (tp1, tp2))
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
  | Eensures _ ->
      error "'ensures' is not allowed nested inside another expression."
  | Eforall (vars, body) | Eexists (vars, body) ->
      let (local_ctx, tvars) = type_params types ctx vars in
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
      | Band | Bor | Biff ->
        if expand_type types type1 = TTBool && expand_type types type2 = TTBool then (TEbinop (b, tex1, tex2), TTBool)
        else error "Expected boolean type variables for this logical operations."
      | Bland | Blor ->
        failwith "Bland/Blor are never produced by parsing."
    end
  | Ecall (f, args)
    when (let n = String.concat "." (List.map (fun id -> id.id) f) in
          List.mem n ["set.empty"; "set.add"; "set.union"; "set.contains"; "set.subset";
                      "set.diff"; "set.cardinal"; "map.empty"; "map.get"; "map.set";
                      "map.const"; "map.contains"; "map.combine"]) ->
      let func_name = String.concat "." (List.map (fun id -> id.id) f) in
      let last_ident = List.hd (List.rev f) in
      type_collection_call expected ctx fns records types func_name args last_ident.loc
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
          let (targ_expr, targ_type) = expr ~expected:param.v_tp ctx fns records types arg in
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
            let expected_type =
              try List.assoc id.id expected_fields
              with Not_found -> error ~loc:id.loc "Field '%s' not part of record." id.id
            in
            let (tex, ttype) = expr ~expected:expected_type ctx fns records types ex in
            if expand_type types ttype <> expand_type types expected_type then
              error ~loc:id.loc "Incorrect type for '%s'." id.id;
            (id.id, tex)
          ) fields in
          (TErecord tfields, TTModuleRecord rec_name)
      | None ->
          begin match fields with
          | [(id, ex)] when id.id = "payload" ->
              let declared_payload_opt = H.find_opt types "payload" in
              let (tex, ttype) = expr ?expected:declared_payload_opt ctx fns records types ex in
              let declared_payload = match declared_payload_opt with Some t -> t | None -> ttype in
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

and type_collection_call expected ctx fns records types func_name args loc =
  let ty ?expected arg = expr ?expected ctx fns records types arg in
  let expand t = expand_type types t in
  let expect_set () = match expected with
    | Some t -> (match expand t with
        | TTSet _ as s -> s
        | _ -> error ~loc "Cannot infer element type for '%s': expected type is not a set." func_name)
    | None -> error ~loc "Cannot infer element type for '%s' without more context." func_name
  in
  let expect_map () = match expected with
    | Some t -> (match expand t with
        | TTMap _ as m -> m
        | _ -> error ~loc "Cannot infer key/value type for '%s': expected type is not a map." func_name)
    | None -> error ~loc "Cannot infer key/value type for '%s' without more context." func_name
  in
  let mismatch () = error ~loc "Argument type mismatch for function '%s'." func_name in
  let mk ret_tp params targs = (TEcall ({ fn_name = func_name; fn_params = params; fn_return = ret_tp }, targs), ret_tp) in
  match func_name, args with
  | "set.empty", [] ->
      let set_tp = expect_set () in
      mk set_tp [] []
  | "set.add", [elem; s] ->
      let (telem, elem_tp) = ty elem in
      let set_tp = TTSet elem_tp in
      let (ts, s_tp) = ty ~expected:set_tp s in
      if expand s_tp <> expand set_tp then mismatch ();
      mk set_tp [{ v_name = "v"; v_tp = elem_tp }; { v_name = "s"; v_tp = set_tp }] [telem; ts]
  | ("set.union" | "set.diff"), [a; b] ->
      let (ta, a_tp) = ty ?expected a in
      let set_tp = (match expand a_tp with TTSet _ -> a_tp | _ ->
        error ~loc "Expected a set argument for '%s'." func_name) in
      let (tb, b_tp) = ty ~expected:set_tp b in
      if expand b_tp <> expand set_tp then mismatch ();
      mk set_tp [{ v_name = "a"; v_tp = set_tp }; { v_name = "b"; v_tp = set_tp }] [ta; tb]
  | "set.subset", [a; b] ->
      let (ta, a_tp) = ty a in
      let set_tp = (match expand a_tp with TTSet _ -> a_tp | _ ->
        error ~loc "Expected a set argument for 'set.subset'.") in
      let (tb, b_tp) = ty ~expected:set_tp b in
      if expand b_tp <> expand set_tp then mismatch ();
      mk TTBool [{ v_name = "a"; v_tp = set_tp }; { v_name = "b"; v_tp = set_tp }] [ta; tb]
  | "set.contains", [elem; s] ->
      let (telem, elem_tp) = ty elem in
      let set_tp = TTSet elem_tp in
      let (ts, s_tp) = ty ~expected:set_tp s in
      if expand s_tp <> expand set_tp then mismatch ();
      mk TTBool [{ v_name = "v"; v_tp = elem_tp }; { v_name = "s"; v_tp = set_tp }] [telem; ts]
  | "set.cardinal", [s] ->
      let (ts, s_tp) = ty s in
      (match expand s_tp with
       | TTSet _ -> mk TTInt [{ v_name = "s"; v_tp = s_tp }] [ts]
       | _ -> error ~loc "Expected a set argument for 'set.cardinal'.")
  | "map.empty", [] ->
      let map_tp = expect_map () in
      mk map_tp [] []
  | "map.get", [k; m] ->
      let (tm, m_tp) = ty m in
      (match expand m_tp with
       | TTMap (k_tp, v_tp) ->
           let (tk, k_tp') = ty ~expected:k_tp k in
           if expand k_tp' <> expand k_tp then mismatch ();
           mk v_tp [{ v_name = "k"; v_tp = k_tp }; { v_name = "m"; v_tp = m_tp }] [tk; tm]
       | _ -> error ~loc "Expected a map argument for 'map.get'.")
  | "map.set", [k; v; m] ->
      (try
        let (tm, m_tp) = ty m in
        match expand m_tp with
        | TTMap (k_tp, v_tp) ->
            let (tk, k_tp') = ty ~expected:k_tp k in
            let (tv, v_tp') = ty ~expected:v_tp v in
            if expand k_tp' <> expand k_tp then mismatch ();
            if expand v_tp' <> expand v_tp then mismatch ();
            mk m_tp [{ v_name = "k"; v_tp = k_tp }; { v_name = "v"; v_tp = v_tp };
                     { v_name = "m"; v_tp = m_tp }] [tk; tv; tm]
        | _ -> error ~loc "Expected a map argument for 'map.set'."
      with Error _ ->
        let (tk, k_tp) = ty k in
        let (tv, v_tp) = ty v in
        let map_tp = TTMap (k_tp, v_tp) in
        let (tm, m_tp) = ty ~expected:map_tp m in
        if expand m_tp <> expand map_tp then mismatch ();
        mk map_tp [{ v_name = "k"; v_tp = k_tp }; { v_name = "v"; v_tp = v_tp };
                   { v_name = "m"; v_tp = map_tp }] [tk; tv; tm])
  | "map.const", [default] ->
      let expected_v = match expected with
        | Some t -> (match expand t with TTMap (_, v_tp) -> Some v_tp | _ -> None)
        | None -> None
      in
      let (tdefault, v_tp) = ty ?expected:expected_v default in
      let k_tp = match expected with
        | Some t -> (match expand t with
            | TTMap (k_tp, _) -> k_tp
            | _ -> error ~loc "Cannot infer key type for 'map.const' without an expected map type.")
        | None -> error ~loc "Cannot infer key type for 'map.const' without an expected map type."
      in
      let map_tp = TTMap (k_tp, v_tp) in
      mk map_tp [{ v_name = "default"; v_tp = v_tp }] [tdefault]
  | "map.contains", [k; m] ->
      let (tm, m_tp) = ty m in
      (match expand m_tp with
       | TTMap (k_tp, _) ->
           let (tk, k_tp') = ty ~expected:k_tp k in
           if expand k_tp' <> expand k_tp then mismatch ();
           mk TTBool [{ v_name = "k"; v_tp = k_tp }; { v_name = "m"; v_tp = m_tp }] [tk; tm]
       | _ -> error ~loc "Expected a map argument for 'map.contains'.")
  | "map.combine", [m1; m2; f] ->
      let (tm1, m1_tp) = ty ?expected m1 in
      let map_tp = (match expand m1_tp with TTMap _ -> m1_tp | _ ->
        error ~loc "Expected a map argument for 'map.combine'.") in
      let (tm2, m2_tp) = ty ~expected:map_tp m2 in
      if expand m2_tp <> expand map_tp then mismatch ();
      let (tf, f_tp) = ty f in
      mk map_tp [{ v_name = "m1"; v_tp = map_tp }; { v_name = "m2"; v_tp = map_tp };
                 { v_name = "f"; v_tp = f_tp }] [tm1; tm2; tf]
  | _, _ -> error ~loc "Incorrect number of arguments for function '%s'." func_name

let extract_vfx_attr (tp : Ast.tp) : string option =
  match tp with
  | Tattribute (_, attr) -> Some attr
  | _ -> None

let resolve_variant (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env)
    (owner_id : Ast.ident) (variant_opt : Ast.expr list option) =
  match variant_opt with
  | None -> None
  | Some exprs ->
      Some (List.map (fun e ->
        let (te, tp) = expr ctx fns records types e in
        if tp <> TTInt then
          error ~loc:owner_id.loc "Variant measure in '%s' must be an integer expression." owner_id.id;
        te
      ) exprs)

let mod_decl (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (d : Ast.modl) : Ast.tmodl list =
  match d with
  | Dtype (id, tp, inv_opt) ->
      let vfx_attr = extract_vfx_attr tp in
      let ttype = resolve_type types tp in
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
          let (inv_ctx, tparams) = type_params types ctx inv_params in
          let (tex, expr_type) = expr inv_ctx fns records types inv_ex in
          if expr_type <> TTBool then
            error ~loc:id.loc "Invariant '%s' result not a boolean." inv_id.id;
          let inv_fn = { fn_name = inv_id.id; fn_params = tparams; fn_return = TTBool } in
          Some (inv_fn, tex)
      in
      [ TDtype (id.id, ttype, tinv, vfx_attr) ]
  | Dval (id, params, tp, ex, vfx_attr, variant_opt, axioms) ->
      let (local_ctx, tparams) = type_params types ctx params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = resolve_type types tp } in
      H.add fns id.id f;
      let (tex, _) = match ex with
        | Eensures ens ->
            H.replace local_ctx "result" { v_name = "result"; v_tp = f.fn_return };
            let (tens, ens_tp) = expr local_ctx fns records types ens in
            if expand_type types ens_tp <> TTBool then
              error ~loc:id.loc "Ensures clause in '%s' must be a boolean expression." id.id;
            (TEensures tens, TTBool)
        | _ -> expr ~expected:f.fn_return local_ctx fns records types ex
      in
      let vfx_param = Option.map (fun (attr_id : Ast.ident) -> attr_id.id) vfx_attr in
      let variant = resolve_variant local_ctx fns records types id variant_opt in
      TDval (f, tex, vfx_param, variant) :: List.map (fun kind -> TDaxiom (kind, id.id)) axioms
  | Dlemma (id, params, body, variant_opt, ensures) ->
      let (local_ctx, tparams) = type_params types ctx params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = TTBool } in
      H.add fns id.id f;
      let (tbody, _) = expr local_ctx fns records types body in
      let tens = List.map (fun e ->
        let (te, _) = expr local_ctx fns records types e in te) ensures in
      let variant = resolve_variant local_ctx fns records types id variant_opt in
      [ TDlemma (f, tbody, variant, tens) ]
  | Daxiom (id, e) ->
      let (te, tp) = expr ctx fns records types e in
      if tp <> TTBool then
        error ~loc:id.loc "Axiom '%s' must be a boolean expression." id.id;
      [ TDassume (id.id, te) ]

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

  let rec rewrite_payload_tp (t : Ast.tp) : Ast.tp = match t with
    | Tcst { id = "payload"; loc } -> Tcst { id = "t"; loc }
    | Tcst _ -> t
    | Tmap (k, v) -> Tmap (rewrite_payload_tp k, rewrite_payload_tp v)
    | Tset v -> Tset (rewrite_payload_tp v)
    | Ttuple (t1, t2) -> Ttuple (rewrite_payload_tp t1, rewrite_payload_tp t2)
    | Trecord fields -> Trecord (List.map (fun (id, tp) -> (id, rewrite_payload_tp tp)) fields)
    | Taccess _ | Tinvariant _ | Tvariant _ -> t
    | TvariantArgs ctors -> TvariantArgs (List.map (fun (id, tp) -> (id, rewrite_payload_tp tp)) ctors)
    | Tattribute (core, attr) -> Tattribute (rewrite_payload_tp core, attr)
  in
  let rec rewrite_payload_expr (e : Ast.expr) : Ast.expr = match e with
    | Ecst _ | Eaccess _ -> e
    | Efield (e, f) -> Efield (rewrite_payload_expr e, f)
    | Etuple (e1, e2) -> Etuple (rewrite_payload_expr e1, rewrite_payload_expr e2)
    | Ebinop (op, l, r) -> Ebinop (op, rewrite_payload_expr l, rewrite_payload_expr r)
    | Enot e -> Enot (rewrite_payload_expr e)
    | Eneg e -> Eneg (rewrite_payload_expr e)
    | Eif (c, e1, e2) -> Eif (rewrite_payload_expr c, rewrite_payload_expr e1, rewrite_payload_expr e2)
    | Ecall (f, args) -> Ecall (f, List.map rewrite_payload_expr args)
    | Erecord fields -> Erecord (List.map (fun (n, e) -> (n, rewrite_payload_expr e)) fields)
    | Ematch (es, cases) -> Ematch (List.map rewrite_payload_expr es,
        List.map (fun (pats, b) -> (pats, rewrite_payload_expr b)) cases)
    | Erequires (r, b) -> Erequires (rewrite_payload_expr r, rewrite_payload_expr b)
    | Erequires_vfx (r, b) -> Erequires_vfx (rewrite_payload_expr r, rewrite_payload_expr b)
    | Eensures e -> Eensures (rewrite_payload_expr e)
    | Eforall (vars, body) ->
        Eforall (List.map (fun (id, tp) -> (id, rewrite_payload_tp tp)) vars, rewrite_payload_expr body)
    | Eexists (vars, body) ->
        Eexists (List.map (fun (id, tp) -> (id, rewrite_payload_tp tp)) vars, rewrite_payload_expr body)
  in

  let rec process_defs defs mdls =
    match defs with
    | [] -> List.rev mdls
    | DefInterface (name, proof, lines) :: rest ->
        H.add interfaces name.id lines;
        let fn_names = List.filter_map (function Ifunc (id, _, _) -> Some id.id | _ -> None) lines in
        let expected = match name.id with
          | "CvRDT" -> Some ["create"; "merge"; "compare"; "equals"]
          | "CmRDT" -> Some ["create"; "execute"; "compare"; "equals"]
          | _ -> None
        in
        (match expected with
         | Some exp when not (List.for_all (fun e -> List.mem e fn_names) exp) ->
             error ~loc:name.loc
               "Interface '%s' must declare at least %s (found %s)."
               name.id (String.concat ", " exp) (String.concat ", " fn_names)
         | _ -> ());
        let abstract_types : type_env = H.create 4 in
        H.replace abstract_types "payload" (TTModuleRecord "t");
        let abstract_fns : fn_env = H.create 8 in
        List.iter (function
          | Ifunc (id, params, tp) ->
              let tparams = List.map (fun (p_id, p_tp) ->
                { v_name = p_id.id; v_tp = expand_type abstract_types (resolve_type abstract_types p_tp) }) params in
              H.replace abstract_fns id.id
                { fn_name = id.id; fn_params = tparams;
                  fn_return = expand_type abstract_types (resolve_type abstract_types tp) }
          | _ -> ()) lines;
        let abstract_records : record_env = H.create 1 in
        let abstract_ctx : var_env = H.create 1 in
        List.iter (function
          | Iaxiom_custom (axiom_id, e) ->
              let e' = rewrite_payload_expr e in
              let (te, tp) = expr abstract_ctx abstract_fns abstract_records abstract_types e' in
              if expand_type abstract_types tp <> TTBool then
                error ~loc:axiom_id.loc
                  "Axiom '%s' declared in interface '%s' must be a boolean expression." axiom_id.id name.id;
              H.replace abstract_axiom_formulas axiom_id.id te
          | _ -> ()) lines;
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
        let tlines = List.concat_map (mod_decl ctx fns records types) lines in
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
        if H.mem fns "create" then begin
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

        let interface_axioms = ref [] in
        begin try
          let expected_lines = H.find interfaces interface.id in
          let has_explicit_t = List.exists (function
            | TDtype ("t", _, _, _) -> true
            | _ -> false) tlines in
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
                let expected_return = resolve_type types expected_tp in
                let return_ok =
                  f.fn_return = expected_return
                  || (has_explicit_t && f.fn_return = TTModuleRecord "t"
                      && expected_return = TTModuleRecord "payload")
                in
                if not return_ok then
                  error ~loc:expected_id.loc "Function '%s' return type does not respect the interface's." expected_id.id;
                if List.length f.fn_params <> List.length expected_params then
                  error ~loc:expected_id.loc "Function '%s' has wrong number of arguments." expected_id.id;
              with Not_found ->
                error ~loc:name.loc "Module '%s' missing function '%s'." name.id expected_id.id
              end
          | Iaxiom _ -> ()
          | Iaxiom_custom (axiom_id, e) ->
              let empty_ctx : var_env = H.create 1 in
              let saved_payload_tp = H.find_opt types "payload" in
              if has_explicit_t then H.replace types "payload" (TTModuleRecord "t");
              let e' = if has_explicit_t then rewrite_payload_expr e else e in
              let (te, tp) = expr empty_ctx fns records types e' in
              (match saved_payload_tp with
               | Some t -> H.replace types "payload" t
               | None -> H.remove types "payload");
              if expand_type types tp <> TTBool then
                error ~loc:axiom_id.loc
                  "Axiom '%s' declared in interface '%s' must be a boolean expression." axiom_id.id interface.id;
              interface_axioms := TDassume (axiom_id.id, te) :: !interface_axioms
          ) expected_lines
        with Not_found -> error ~loc:interface.loc "Interface '%s' does not exist." interface.id
        end;
        let tlines = tlines @ List.rev !interface_axioms in

        let tmodl = TDefModule (name.id, interface.id, (H.find interfaces interface.id), tlines) in
        process_defs rest (tmodl :: mdls)
  in
  process_defs p []
