type location = Lexing.position * Lexing.position

type ident = { loc: location; id: string; }

type binop =
  | Badd | Bsub | Bmul | Bdiv
  | Beq | Bneq | Blt | Ble | Bgt | Bge
  | Band | Bor | Biff
  | Bland | Blor

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

type case = ident * ident option list

type expr =
  | Ecst of constant
  | Eaccess of ident list
  | Efield of expr * ident
  | Ebinop of binop * expr * expr
  | Enot of expr
  | Eneg of expr
  | Eif of expr * expr * expr
  | Ecall of ident list * expr list
  | Erecord of (ident * expr) list
  | Ematch of expr list * (case list * expr) list
  | Erequires of expr * expr
  | Erequires_vfx of expr * expr
  | Eensures of expr
  | Eforall of (ident * tp) list * expr
  | Eexists of (ident * tp) list * expr

type intf =
  | Itype of ident
  | Ifunc of ident * param list * tp
  | Iaxiom of ident * ident

type invariant = ident * param list * expr

type modl =
  | Dtype of ident * tp * invariant option
  | Dval of ident * param list * tp * expr * ident option * expr list option * string list
  | Dlemma of ident * param list * expr * expr list option * expr list
  | Daxiom of ident * expr

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

type tcase = string * var option list

type texpr =
  | TEcst of constant
  | TEvar of var
  | TEfield of texpr * string
  | TEbinop of binop * texpr * texpr
  | TEnot of texpr
  | TEneg of texpr
  | TEif of texpr * texpr * texpr
  | TEcall of fn * texpr list
  | TErecord of (string * texpr) list
  | TEmatch of texpr list * (tcase list * texpr) list
  | TErequires of texpr * texpr
  | TErequires_vfx of texpr * texpr
  | TEensures of texpr
  | TElet of string * texpr * texpr
  | TEforall of var list * texpr
  | TEexists of var list * texpr

type tinvariant = fn * texpr

type tmodl =
  | TDtype of string * ttp * tinvariant option * string option
  | TDval of fn * texpr * string option * texpr list option
  | TDlemma of fn * texpr * texpr list option * texpr list
  | TDaxiom of string * string
  | TDassume of string * texpr

type tdef =
  | TDefInterface of string * bool * intf list
  | TDefModule of string * string * intf list * tmodl list

type tfile = tdef list
