type location = Lexing.position * Lexing.position

type ident = { loc: location; id: string; }

type binop =
  | Badd | Bsub | Bmul | Bdiv
  | Beq | Bneq | Blt | Ble | Bgt | Bge
  | Band | Bor

type constant =
  | Cnone
  | Cbool of bool
  | Cstring of string
  | Cint of int64

type tp =
  | Tcst of ident
  | Taccess of ident list
  | Tmap of tp * tp
  | Tset of tp
  | Trecord of (ident * tp) list
  | Tinvariant of ident list
  | Tvariant of ident list
  | TvariantArgs of (ident * tp) list
  | Tattribute of tp * string

type param = ident * tp

type expr =
  | Ecst of constant
  | Eaccess of ident list
  | Ebinop of binop * expr * expr
  | Enot of expr
  | Ecall of ident list * expr list
  | Erecord of (ident * expr) list
  | Ematch of expr * (ident * ident option * expr) list

type intf =
  | Itype of ident
  | Ifunc of ident * param list * tp
  | Iaxiom of ident * ident

type invariant = ident * param list * expr

type modl =
  | Dtype of ident * tp * invariant option
  | Dval of ident * param list * tp * expr * (ident * tp) option

type modl_param = ident * ident

type def =
  | DefInterface of ident * bool * intf list
  | DefModule of ident * modl_param list * ident * modl list

type file = def list

type ttp =
  | TTInt
  | TTBool
  | TTMap of ttp * ttp
  | TTSet of ttp
  | TTAbstract of string
  | TTRecord of (string * ttp) list
  | TTInvariant of string list
  | TTModuleRecord of string
  | TTVariant of string * string list
  | TTVariantArgs of string * (string * ttp) list

type var = {
  v_name: string;
  v_tp: ttp;
}

type fn = {
  fn_name: string;
  fn_params: var list;
  fn_return: ttp;
}

type texpr =
  | TEcst of constant
  | TEvar of var
  | TEbinop of binop * texpr * texpr
  | TEnot of texpr
  | TEcall of fn * texpr list
  | TErecord of (string * texpr) list
  | TEmatch of texpr * (string * string option * texpr) list

type tinvariant = fn * texpr

type tmodl =
  | TDtype of string * ttp * tinvariant option * string option
  | TDval of fn * texpr * (string * ttp) option

type tdef =
  | TDefInterface of string * bool * intf list
  | TDefModule of string * string * intf list * tmodl list

type tfile = tdef list