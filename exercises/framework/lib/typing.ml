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
  | Tcst { id = payload; _ } -> TTModuleRecord payload
  | Tmap (t1, t2) -> TTMap (resolve_type t1, resolve_type t2)
  | Trecord fields -> 
      let tfields = List.map (fun (id, tp) -> (id.id, resolve_type tp)) fields in
      TTRecord tfields
  | Taccess path -> 
      let full_path = String.concat "." (List.map (fun id -> id.id) path) in
      TTModuleRecord full_path
  | Tinvariant inv ->
      let string_path = List.map (fun id -> id.id) inv in
      TTInvariant string_path

let rec expand_type (types : type_env) (tp : ttp) : ttp =
  match tp with
  | TTModuleRecord name ->
      begin try
        expand_type types (H.find types name)
        with Not_found -> tp
      end
  | TTMap (k, v) -> TTMap (expand_type types k, expand_type types v)
  | TTRecord fields -> TTRecord (List.map (fun (n, t) -> (n, expand_type types t)) fields)
  | _ -> tp

let rec expr (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (ex : Ast.expr) : Ast.texpr * Ast.ttp =
  match ex with
  | Ecst (Cint c) -> (TEcst (Cint c), TTInt)
  | Ecst (Cbool b) -> (TEcst (Cbool b), TTBool)
  | Ecst _ -> error "Const not supported."
  | Eaccess path -> begin
      let first_ident = List.hd path in
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
                  (TEvar { v_name = String.concat "." (List.map (fun id -> id.id) path); v_tp = field_type }, field_type)
                with Not_found ->
                  error ~loc:field_ident.loc "Field '%s' does not exist in '%s'." field_ident.id type_name
                end
              with Not_found ->
                error ~loc:first_ident.loc "Definition '%s' does not exist." type_name
              end
          | _ -> error ~loc:first_ident.loc "Variable '%s' is not a record." first_ident.id
          end
      with Not_found -> error ~loc:first_ident.loc "Undeclared variable: '%s'." first_ident.id
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
        let targs = List.map2 (fun arg param ->
          let (targ_expr, targ_type) = expr ctx fns records types arg in
          if expand_type types targ_type <> expand_type types param.v_tp then
            error ~loc: last_ident.loc "Argument type error for function '%s'." func_name
          else targ_expr
        ) args f.fn_params in
        (TEcall (f, targs), f.fn_return)
    with Not_found -> error ~loc:last_ident.loc "Undeclared function: '%s'." func_name
    end
  | Erecord fields ->
      (* TODO: penso que falta corrigir *)
      begin try
        let expected_fields = H.find records "payload" in
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
        (TErecord tfields, TTModuleRecord "payload")
      with Not_found ->
        error "payload definition not found for this module."
      end
  | Ematch (main_ex, cases) ->
      let (tmain_ex, _main_type) = expr ctx fns records types main_ex in
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

let mod_decl (ctx : var_env) (fns : fn_env) (records : record_env) (types : type_env) (d : Ast.modl) : Ast.tmodl =
  match d with
  | Dtype (id, tp, inv_opt) ->
      let ttype = resolve_type tp in
      H.replace types id.id ttype;
      begin match ttype with
      | TTRecord fields -> H.add records id.id fields
      | _ -> ()
      end;
      let tinv = match inv_opt with
        | None  -> None
        | Some (inv_id, inv_params, inv_ex) ->
          let inv_ctx = H.create 4 in
          let tparams = List.map (fun (param_id, param_tp) ->
            let v = { v_name = param_id.id; v_tp = resolve_type param_tp } in
            H.add inv_ctx param_id.id v;
            v
          ) inv_params in
          let (tex, expr_type) = expr inv_ctx fns records types inv_ex in
          if expr_type <> TTBool then
            error ~loc:id.loc "Invarinat '%s' result not a boolean." inv_id.id;
          let inv_fn = { fn_name = inv_id.id; fn_params = tparams; fn_return = TTBool } in
          Some (inv_fn, tex)
      in
      TDtype (id.id, ttype, tinv)
  | Dval (id, params, tp, ex) ->
      let tparams = List.map (fun (p_id, p_tp) ->
        let v = { v_name = p_id.id; v_tp = resolve_type p_tp } in
        H.add ctx p_id.id v;
        v
      ) params in
      let f = { fn_name = id.id; fn_params = tparams; fn_return = resolve_type tp } in
      H.add fns id.id f;
      let (tex, _) = expr ctx fns records types ex in
      TDval (f, tex)

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
  
  let rec process_defs defs mdls =
    match defs with
    | [] -> List.rev mdls
    | DefInterface (name, lines) :: rest ->
        H.add interfaces name.id lines;
        let tdef = TDefInterface (name.id, lines) in
        process_defs rest (tdef :: mdls)
    | DefModule (name, _params, interface, lines) :: rest ->
        H.clear ctx;
        H.clear fns;
        List.iter (fun (name, f) -> H.add fns name f) builtin_fns;
        H.clear records;
        H.clear types;
        let tlines = List.map (mod_decl ctx fns records types) lines in

        begin try
          let exepected_lines = H.find interfaces interface.id in
          List.iter (fun req ->
            match req with
            | Itype expected_id ->
              let found = List.exists (function
                | TDtype (tname, _, _) -> tname = expected_id.id
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
          | Iaxiom _ -> () (* axioms are handled by the printer *)
          ) exepected_lines
        with Not_found -> error ~loc:interface.loc "Interface '%s' does not exist." interface.id
        end;

        let tmodl = TDefModule (name.id, interface.id, (H.find interfaces interface.id), tlines) in
        process_defs rest (tmodl :: mdls)
  in
  process_defs p []