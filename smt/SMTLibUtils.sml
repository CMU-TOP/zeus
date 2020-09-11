structure SMTLibUtils : SMT_LIB_UTILS = 
struct
  open SMTLib

  (* ["a", "b"] -> "(a b)" *)
  fun parens strings = "(" ^ String.concatWith " " strings ^ ")"

  fun sorted_var_to_string (sym, sort) = parens [sym, sort]

  val pattern_to_string = fn
    [] => raise Fail "malformed pattern"
  | [sym] => sym
  | syms => parens syms

  fun int_to_string i = String.map (fn #"~" => #"-" | c => c) (Int.toString i)

  val rec term_to_string = fn
    Const s => int_to_string s
  | String s => "\"" ^ s ^ "\""
  | Ident s => s
  | App (sym, terms) => parens (sym :: map term_to_string terms)
  | Let (bindings, term) => parens [
      "let",
      parens (map (fn (x, t) => parens [x, term_to_string t]) bindings),
      term_to_string term
    ]
  | ForAll (vars, term) => parens [
      "forall",
      parens (map sorted_var_to_string vars),
      term_to_string term
    ]
  | Exists (vars, term) => parens [
      "exists",
      parens (map sorted_var_to_string vars),
      term_to_string term
    ]
  | Match (term, match_cases) => raise Fail "match not supported"
    (* Z3 currently has a bug that doesn't let us use this syntax
    parens [
      "match",
      term_to_string term,
      parens (map (fn (pattern, term) =>
        parens [pattern_to_string pattern, term_to_string term]
      ) match_cases)
    ]*)
  | True => "true"
  | False => "false"
  | Not term => parens [
      "not",
      term_to_string term
    ]
  | Implies terms => parens ("=>" :: map term_to_string terms)
  | And terms => parens ("and" :: map term_to_string terms)
  | Or terms => parens ("or" :: map term_to_string terms)
  | Equals terms => parens ("=" :: map term_to_string terms)
  | Distinct terms => parens ("distinct" :: map term_to_string terms)
  | IfThenElse (t1, t2, t3) => parens ("ite" :: map term_to_string [t1, t2, t3])
  | Test (s, t) => parens [parens ["_", "is", s], term_to_string t]

  val command_to_string = fn
    DeclareSort sort => parens ["declare-sort", sort]
  | DeclareFun (sym, sorts, sort) => parens [
      "declare-fun",
      sym,
      parens sorts,
      sort
    ]
  | DefineFun (sym, sorted_vars, sort, term) => parens [
      "define-fun",
      sym,
      parens (map sorted_var_to_string sorted_vars),
      sort,
      term_to_string term
    ]
  | DeclareConst (sym, sort) => parens [
      "declare-const",
      sym,
      sort
    ]
  | DeclareDatatype (sym, cons) => parens [
      "declare-datatype",
      sym,
      parens (map (fn (con, params) => parens (
        con :: map sorted_var_to_string params
      )) cons)
    ]
  | Assert term => parens [
      "assert",
      term_to_string term
    ]
  | CheckSat => parens ["check-sat"]

  fun append_newline s = s ^ "\n"

  fun write_commands_to_file path commands =
    let val outstream = TextIO.openOut path in
      List.app (Fn.curry TextIO.output outstream o (append_newline o command_to_string)) commands;
      TextIO.closeOut outstream
    end

  fun read_response_from_file path =
    let val instream = TextIO.openIn path in
      (case TextIO.inputLine instream of
        NONE => raise Fail ("unable to get input from " ^ path)
      | SOME x =>
      if String.isPrefix "sat" x then Sat else
      if String.isPrefix "unsat" x then Unsat else
      raise Fail ("unrecognized response: " ^ x))
      before TextIO.closeIn instream
    end
end
