structure SMTLib = struct

  type symbol = string
  type sort = string
  type sorted_var = symbol * sort
  type pattern = symbol list

  datatype term = 
    Const of int
  | String of string
  | Ident of symbol
  | App of symbol * term list
  | Let of (symbol * term) list * term
  | ForAll of sorted_var list * term
  | Exists of sorted_var list * term
  | Match of term * (pattern * term) list
  | True | False
  | Not of term
  | Implies of term list
  | And of term list
  | Or of term list
  | Equals of term list
  | Distinct of term list
  | IfThenElse of term * term * term
  | Test of symbol * term (* tester application *)

  datatype command =
    DeclareSort of symbol
  | DeclareFun of symbol * sort list * sort
  | DefineFun of symbol * sorted_var list * sort * term
  | DeclareConst of symbol * sort
  | DeclareDatatype of symbol * (symbol * (symbol * sort) list) list
  | Assert of term
  | CheckSat

  datatype response = Sat | Unsat

end
