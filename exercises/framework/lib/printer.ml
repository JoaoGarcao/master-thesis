open Format
open Ast

(* ─── Helpers ────────────────────────────────────────────────────────────── *)

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

(* ─── Name derivation ────────────────────────────────────────────────────── *)

let strip_crdt_suffix name =
  match String.split_on_char '_' name with
  | base :: _ -> base
  | []        -> name

let uppercase_initials name =
  let buf = Buffer.create 4 in
  String.iter (fun c -> if c >= 'A' && c <= 'Z' then Buffer.add_char buf c) name;
  Buffer.contents buf

(* e.g. "GCounter_CRDT" -> aux_mod="GCAuxiliary", main_mod="GCounter", alias="GCAux" *)
let derive_names mod_name =
  let base     = strip_crdt_suffix mod_name in
  let initials = uppercase_initials base in
  (initials ^ "Auxiliary", base, initials ^ "Aux")

(* ─── Use-clause analysis ────────────────────────────────────────────────── *)

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

(* ─── Type translation ──────────────────────────────────────────────────── *)

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
  | TTModuleRecord m  -> pp_print_string ppf m

(* ─── Expression translation ────────────────────────────────────────────── *)

let rec pp_w3_texpr ppf = function
  | TEcst c            -> pp_constant ppf c
  | TEvar v            -> pp_print_string ppf v.v_name
  | TEbinop (op, l, r) ->
      fprintf ppf "@[<hv 1>%a@ %a@ %a@]" pp_w3_texpr l pp_w3_binop op pp_w3_texpr r
  | TEcall (fn, args)  ->
      fprintf ppf "@[<h>%s@ %a@]"
        fn.fn_name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_w3_texpr_atom) args
  | TErecord fields    ->
      fprintf ppf "{ @[<hv>%a@] }"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, e) -> fprintf ppf "%s = %a" name pp_w3_texpr e))
        fields
  | TEmatch (e, arms)  ->
      fprintf ppf "@[<v>match %a with@ %a@ end@]"
        pp_w3_texpr e
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ")
          (fun ppf (name, body) ->
            fprintf ppf "@[<hv 2>| %s ->@ %a@]" name pp_w3_texpr body))
        arms

and pp_w3_texpr_atom ppf e = match e with
  | TEcst _ | TEvar _ -> pp_w3_texpr ppf e
  | _                 -> fprintf ppf "(%a)" pp_w3_texpr e

(* ─── Parameter translation ─────────────────────────────────────────────── *)

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

(* ─── Use clauses ───────────────────────────────────────────────────────── *)

let pp_w3_uses ppf () =
  if !uses_int_int && !uses_min_max then
    fprintf ppf "use int.Int, int.MinMax@ @ "
  else if !uses_int_int then
    fprintf ppf "use int.Int@ @ "

(* ─── Predicate detection ───────────────────────────────────────────────── *)

let is_bool_ttp = function TTBool -> true | _ -> false

(* ─── Interface helpers ─────────────────────────────────────────────────── *)

let interface_fn_names intfs =
  List.filter_map (function
    | Ifunc (id, _, _) -> Some id.id
    | Itype _ | Iaxiom _ -> None) intfs

let is_two_module_interface intfs =
  let fns = interface_fn_names intfs in
  List.mem "merge" fns && List.mem "compare" fns

(* ─── Body rewriting for Auxiliary ─────────────────────────────────────── *)

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

(* ─── Auxiliary module decls ────────────────────────────────────────────── *)

let pp_w3_aux_decl ppf = function
  | TDtype ("payload", tp, _) ->
      fprintf ppf "@[type payload = %a@]" pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = { payload: %a; }@]" pp_w3_ttp tp;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let function get_payload (a: t) : %a@ = t.payload@]" pp_w3_ttp tp

  | TDtype (name, tp, _) ->
      fprintf ppf "@[type %s = %a@]" name pp_w3_ttp tp

  | TDval ({ fn_name = "init_state"; _ }, body) ->
      fprintf ppf "@[<v 2>let function create () : t@ = { payload = %a }@]"
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
      if is_bool_ttp fn.fn_return then
        fprintf ppf "@[<v 2>predicate %s %a@ = %a@]"
          fn.fn_name pp_w3_tparams tparams pp_w3_texpr rewritten
      else
        fprintf ppf "@[<v 2>let function %s %a : %a@ = { payload = %a }@]"
          fn.fn_name pp_w3_tparams tparams pp_w3_ttp ret pp_w3_texpr rewritten

(* ─── Auxiliary module ──────────────────────────────────────────────────── *)

let pp_w3_auxiliary ppf aux_mod intfs decls =
  reset_uses ();
  List.iter scan_tmodl decls;
  let aux_only_exclude = List.filter_map (function
    | Ifunc (id, _, _) when id.id = "equals" -> Some id.id
    | _ -> None) intfs in
  let aux_decls = List.filter (function
    | TDval (fn, _) -> not (List.mem fn.fn_name aux_only_exclude)
    | _ -> true) decls in
  fprintf ppf "@[<v 2>module %s@ @ %a%a@]@ @ end@ "
    aux_mod
    pp_w3_uses ()
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_aux_decl) aux_decls

(* ─── Main module delegates ─────────────────────────────────────────────── *)

let pp_w3_main_decl ppf (aux_alias, payload_tp, tmodl) =
  match tmodl with
  | TDtype ("payload", _, _) ->
      fprintf ppf "@[type payload = %s.payload@]" aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[type t = %s.t@]" aux_alias

  | TDtype (name, _, _) ->
      fprintf ppf "@[type %s = %s.%s@]" name aux_alias name

  | TDval ({ fn_name = "init_state"; _ }, _) ->
      fprintf ppf "@[<v 2>let function get_payload (t: t) : %a@ = %s.get_payload t@]"
        pp_w3_ttp payload_tp aux_alias;
      fprintf ppf "@ @ ";
      fprintf ppf "@[<v 2>let function create () : t@ = %s.create ()@]" aux_alias

  | TDval ({ fn_name = "equals"; _ }, _) ->
      (* equals is always defined locally in the main module *)
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

(* ─── Top-level ─────────────────────────────────────────────────────────── *)

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
  | Tcst { id = "payload"; _ } -> TTModuleRecord "payload"
  | _ -> TTModuleRecord "t"

let pp_w3_intf_decl ppf = function
  | Itype id ->
      fprintf ppf "@[type %s@]" id.id
  | Ifunc (id, [], _tp) ->
      if id.id = "init_state" then
        fprintf ppf "@[val ghost function create () : t@]"
      else
        fprintf ppf "@[val function %s (t: t) : payload@]" id.id
  | Ifunc (id, _params, tp) ->
      if is_bool_ttp (resolve_intf_tp tp) then
        fprintf ppf "@[predicate %s t t@]" id.id
      else
        fprintf ppf "@[function %s t t : t@]" id.id
  | Iaxiom _ -> ()

let pp_w3_interface ppf (name, intfs) =
  let types = List.filter (function Itype _ -> true | _ -> false) intfs in
  let funcs = List.filter (function
    | Ifunc (id, _, _) -> id.id <> "equals" && id.id <> "init_state"
    | _ -> false) intfs in
  fprintf ppf "@[<v 2>module %s@ @ %a@ @ @[type t@]@ @ @[val ghost function create () : t@]@ @ @[val function get_payload (a: t) : payload@]@ @ %a@ @ @[<v>predicate equals (a b: t)@ = compare a b /\\ compare b a@]%a@]@ @ end@ "
    name
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_intf_decl) types
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_intf_decl) funcs
    pp_w3_axioms intfs
let pp_w3_tdef ppf = function
  | TDefInterface (name, intfs) ->
      pp_w3_interface ppf (name, intfs)
  | TDefModule (name, sig_name, intfs, decls) ->
      let (aux_mod, main_mod, aux_alias) = derive_names name in
      if is_two_module_interface intfs then begin
        pp_w3_auxiliary ppf aux_mod intfs decls;
        fprintf ppf "@ @ ";
        pp_w3_main ppf (main_mod, sig_name, aux_mod, aux_alias, intfs, decls)
      end else begin
        reset_uses ();
        List.iter scan_tmodl decls;
        fprintf ppf "@[<v 2>module %s : %s@ @ %a%a@]@ @ end@ "
          main_mod sig_name
          pp_w3_uses ()
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ @ ") pp_w3_aux_decl) decls
      end

let pp_w3_tfile ppf defs =
  fprintf ppf "@[<v>%a@]@."
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") pp_w3_tdef) defs

(* ─── Public interface ──────────────────────────────────────────────────── *)

let print_w3_tfile tfile = pp_w3_tfile std_formatter tfile
let write_w3_tfile fmt tfile = pp_w3_tfile fmt tfile