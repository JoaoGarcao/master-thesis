%{
  open Ast
%}

%token <Ast.constant> CST
%token <string> IDENT

%token MODULE INTERFACE TYPE VAL AXIOM INVARIANT END
%token MATCH WITH MAP

%token LP RP
%token LB RB
%token COMMA EQUAL COLON DOT BAR ARROW
%token EOF

%token PLUS MINUS TIMES DIV
%token EQ NEQ LT LE GT GE
%token AND OR

%left OR
%left AND
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIV

%start file
%type <Ast.file> file

%%

file:
| dl = list(def) EOF
    { dl }
;

def:
| INTERFACE id = ident dl = list(intf_decl) END
    { DefInterface (id, dl) }
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
| VAL id = ident params = val_params COLON t = tp EQUAL e = expr
    { Dval (id, params, t, e) }
;

invariant_decl:
| INVARIANT id = ident params = val_params EQUAL e = expr
    { (id, params, e) }
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
| path = separated_nonempty_list(DOT, ident)
    { if List.length path = 1 then Tcst (List.hd path) else Taccess path }
| MAP LT t1 = tp COMMA t2 = tp GT
    { Tmap (t1, t2) }
| LB fields = separated_list(COMMA, record_param_tp) RB
    { Trecord fields }
;

record_param_tp:
| id = ident COLON t = tp
    { (id, t) }
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
| MATCH e = expr WITH cases = nonempty_list(match_case) END
    { Ematch (e, cases) }
| LP e = expr RP
    { e }
;

record_param_expr:
| id = ident COLON e = expr
    { (id, e) }
;

match_case:
| BAR id = ident ARROW e = expr
    { (id, e) }
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
  id = IDENT { { loc = ($startpos, $endpos); id } }
;