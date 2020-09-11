structure SimplifiedUtils = 
struct
  structure S = SimplifiedSyntax

  val constToString =
    fn (S.INT (_, s) | S.WORD (_, s) | S.STRING s | S.CHAR s | S.REAL s) => s

  val rec patternToString = fn
    S.WildcardPat t => "_"
  | S.VarPat (x, t) => Symbol.toString x
  | S.RecordPat (rows, t) =>
    "{" ^
    String.concatWith ", "
      (map (fn (label, pat) => label ^ "=" ^ patternToString pat) rows) ^
    "}"
  | S.AsPat (x, pat, t) =>
    Symbol.toString x ^ " as " ^ patternToString pat
  | S.ConstPat (c, t) => constToString c
  | S.ConPat (con, pat, t) => con ^ " " ^ patternToString pat

  fun toStringLimited 0 = Fn.const "..."
    | toStringLimited n = fn
      S.Const (c, t) => constToString c
    | S.Var (x, t) => Symbol.toString x
    | S.Record (rows, t) => 
      "{" ^
      String.concatWith ", "
        (map (fn (label, exp) => label ^ "=" ^ toStringLimited (n-1) exp) rows) ^
      "}"
    | S.Proj (exp, label, t) =>
      "(" ^ toStringLimited (n-1) exp ^ ")" ^ "." ^ label
    | S.Inj (label, exp, t) =>
      label ^ "(" ^ toStringLimited (n-1) exp ^ ")"
    | S.Case (exp1, match, is_exhaustive, t) =>
      "case " ^ toStringLimited (n-1) exp1 ^ " of " ^
      String.concatWith " | "
      (map (fn (sumpat, exp) =>
        patternToString sumpat ^ " => " ^ toStringLimited (n-1) exp
      ) match)
    | S.Lambda (x, exp, t) =>
      "(fn " ^ Symbol.toString x ^ " => " ^ toStringLimited (n-1) exp ^ ")"
    | S.App (exp1, exp2, t) => toStringLimited (n-1) exp1 ^ " " ^ toStringLimited (n-1) exp2
    | S.Fix (x, exp, t) => "fix " ^ Symbol.toString x ^ " is " ^ toStringLimited (n-1) exp
    | S.Raise (exp, t) => "raise " ^ toStringLimited (n-1) exp
    | S.Handle (exp1, (x, exp2), t) =>
      toStringLimited (n-1) exp1 ^ " handle " ^
      Symbol.toString x ^ " => " ^ toStringLimited (n-1) exp2

  val toString = toStringLimited ~1

  val toStringShallow = toStringLimited 1

end
