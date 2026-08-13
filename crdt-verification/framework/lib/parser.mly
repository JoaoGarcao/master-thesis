%{
  open Ast
%}

%token <Ast.constant> CST
%token <string> IDENT
%token <string> VFX_ATTR

%token MODULE INTERFACE TYPE VAL AXIOM INVARIANT END PROOF VARIANT
%token MATCH WITH MAP
%token IF THEN ELSE
%token LEMMA ENSURES REQUIRES
%token FORALL EXISTS

%token LP RP
%token LB RB
%token COMMA EQUAL COLON DOT BAR ARROW
%token EOF

%token PLUS MINUS TIMES DIV
%token EQ NEQ LT LE GT GE
%token AND OR NOT

%left OR
%left AND
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIV
%nonassoc NOT
%nonassoc unary_minus

%start file
%type <Ast.file> file

%%

file:
| dl = list(def) EOF
    { dl }
;

def:
| INTERFACE id = ident proof = boption(PROOF) dl = list(intf_decl) END
    { DefInterface (id, proof, dl) }
| MODULE id = ident params = modl_params COLON intf = ident dl = list(modl_decl) END
    { DefModule (id, params, intf, dl) }
;

modl_params:
| 
    { [] }
| LP params = separated_list(COMMA, modl_param) RP
    { params }
;

modl_param:
| k = ident COLON v = ident
    { (k, v) }
;

intf_decl:
| TYPE id = ident
    { Itype id }
| VAL id = ident params = val_params COLON t = tp
    { Ifunc (id, params, t) }
| AXIOM prop = ident LP func = ident RP
    { Iaxiom (prop, func) }
;

modl_decl:
| TYPE id = ident EQUAL t = tp inv = option(invariant_decl)
    { Dtype (id, t, inv) }
| TYPE id = ident
    { Dtype (id, Tcst id, None) }
| VAL id = ident params = val_params attr = option(vfx_attr) COLON t = tp variant = variant_opt EQUAL e = expr
    { Dval (id, params, t, e, attr, variant) }
| VAL id = ident params = val_params attr = option(vfx_attr) COLON t = tp variant = variant_opt
    { Dval (id, params, t, Ecst Cnone, attr, variant) }
| LEMMA id = ident params = val_params variant = variant_opt ens = ensures_clauses EQUAL e = expr
    { Dlemma (id, params, e, variant, ens) }
;

ensures_clauses:
|
    { [] }
| ENSURES LB e = expr RB rest = ensures_clauses
    { e :: rest }
;

variant_opt:
|
    { None }
| VARIANT LP vs = separated_nonempty_list(COMMA, ident) RP
    { Some vs }
;

invariant_decl:
| INVARIANT id = ident params = val_params EQUAL e = expr
    { (id, params, e) }
;

vfx_attr:
| attr = VFX_ATTR
    { { loc = (Lexing.dummy_pos, Lexing.dummy_pos); id = String.trim attr } }
;

val_params:
| 
    { [] }
| LP params = separated_list(COMMA, param_group) RP
    { List.flatten params }
;

param_group:
| ids = nonempty_list(ident) COLON t = tp
    { List.map (fun id -> (id, t)) ids }
;

tp:
| id = ident DOT path_rest = separated_nonempty_list(DOT, ident)
    { Taccess (id :: path_rest) }
| id = ident
    { Tcst id }
| kw = ident elem = ident
    { if kw.id = "set" then Tset (Tcst elem)
      else failwith ("unexpected type application: " ^ kw.id ^ " " ^ elem.id) }
| MAP LT t1 = tp COMMA t2 = tp GT
    { Tmap (t1, t2) }
| LB fields = separated_list(COMMA, record_param_tp) RB
    { Trecord (List.flatten fields) }
| v = ident BAR vs = separated_nonempty_list(BAR, ident)
    { Tvariant (v :: vs) }
| v = ident COLON t = tp_atom BAR rest = separated_nonempty_list(BAR, variant_arg)
    { TvariantArgs ((v, t) :: rest) }
| core = tp attr = VFX_ATTR
    { Tattribute (core, attr) }
;

tp_atom:
| id = ident DOT path_rest = separated_nonempty_list(DOT, ident)
    { Taccess (id :: path_rest) }
| id = ident
    { Tcst id }
| MAP LT t1 = tp COMMA t2 = tp GT
    { Tmap (t1, t2) }
| LB fields = separated_list(COMMA, record_param_tp) RB
    { Trecord (List.flatten fields) }
;

variant_arg:
| id = ident COLON t = tp_atom
    { (id, t) }
;

record_param_tp:
| id = ident COLON t = tp
    { [(id, t)] }
| id1 = ident id2 = ident COLON t = tp
    { [(id1, t); (id2, t)] }
;

expr:
| c = CST
    { Ecst c }
| path = separated_nonempty_list(DOT, ident)
    { Eaccess path }
| e1 = expr o = binop e2 = expr
    { Ebinop (o, e1, e2) }
| path = separated_nonempty_list(DOT, ident) LP args = separated_list(COMMA, expr) RP
    { Ecall (path, args) }
| LB fields = separated_list(COMMA, record_param_expr) RB
    { Erecord fields }
| MATCH elems = separated_nonempty_list(COMMA, expr) WITH cases = nonempty_list(match_case) END
    { Ematch (elems, cases) }
| IF c = expr THEN e1 = expr ELSE e2 = expr
    { Eif (c, e1, e2) }
| NOT e = expr %prec NOT
    { Enot e }
| MINUS e = expr %prec unary_minus
    { Eneg e }
| REQUIRES LB req = expr RB body = expr
    { Erequires (req, body) }
| REQUIRES LB req = expr RB _attr = VFX_ATTR body = expr
    { Erequires_vfx (req, body) }
| FORALL LP vars = separated_nonempty_list(COMMA, quantifier_var) RP LB body = expr RB
    { Eforall (vars, body) }
| EXISTS LP vars = separated_nonempty_list(COMMA, quantifier_var) RP LB body = expr RB
    { Eexists (vars, body) }
| LP e = expr RP
    { e }
| LP e = expr RP DOT rest = separated_nonempty_list(DOT, ident)
    { List.fold_left (fun acc id -> Efield (acc, id)) e rest }
;

record_param_expr:
| id = ident COLON e = expr
    { (id, e) }
;

quantifier_var:
| id = ident COLON t = tp
    { (id, t) }
;

match_case:
| BAR args = separated_nonempty_list(COMMA, case) ARROW e = expr
    { (args, e) }
;

case:
| id = ident vars = list(var_analyzer)
    { (id, vars) }
;

var_analyzer:
| v = ident { if v.id = "_" then None else Some v }
;

%inline binop:
| PLUS  { Badd }
| MINUS { Bsub }
| TIMES { Bmul }
| DIV   { Bdiv }
| EQ    { Beq }
| NEQ   { Bneq }
| LT    { Blt }
| LE    { Ble }
| GT    { Bgt }
| GE    { Bge }
| AND   { Band }
| OR    { Bor }
;

ident:
  | id = IDENT { { loc = ($startpos, $endpos); id } }
  | MAP        { { loc = ($startpos, $endpos); id = "map" } }
;
