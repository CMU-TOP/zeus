structure SimplifiedSyntax = 
struct
  datatype exhaustive = EXHAUSTIVE | NONEXHAUSTIVE
  datatype base = DEC | HEX
  datatype const =
    INT of base * string
  | WORD of base * string
  | STRING of string
  | CHAR of string
  | REAL of string

  datatype pat =
    WildcardPat of Symbol.typescheme
  | VarPat of (Symbol.t * Symbol.typescheme)
  | RecordPat of ((string * pat) list * Symbol.typescheme)
  | AsPat of (Symbol.t * pat * Symbol.typescheme)
  | ConstPat of (const * Symbol.typescheme)
  | ConPat of (string * pat * Symbol.typescheme)

  datatype exp =
    Const of (const * Symbol.typescheme)
  | Var of (Symbol.t * Symbol.typescheme)
  | Record of ((string * exp) list * Symbol.typescheme)
  | Proj of (exp * string * Symbol.typescheme)
  | Inj of (string * exp * Symbol.typescheme)
  | Case of (exp * (pat * exp) list * exhaustive * Symbol.typescheme)
  | Lambda of (Symbol.t * exp * Symbol.typescheme)
  | App of (exp * exp * Symbol.typescheme)
  | Fix of (Symbol.t * exp * Symbol.typescheme)
  | Raise of (exp * Symbol.typescheme)
  | Handle of (exp * (Symbol.t * exp) * Symbol.typescheme)
end
