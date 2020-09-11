structure Graph =
struct
  structure A = Annotation
  structure SP = SyntaxProgram
  structure SM = SyntaxModule
  structure SC = SyntaxCore

  datatype stringTree = Node of string * stringTree list

  local
    val counter = ref 0
  in
    fun newString () = (
      counter := !counter + 1;
      Int.toString (!counter)
    )
  end

  fun programToTopDecList program =
    case A.syntax program of
      SP.Program (topDec, NONE) => [topDec]
    | SP.Program (topDec, SOME program') => topDec :: programToTopDecList program'

  fun topDecToStrDecList topDec =
    case A.syntax topDec of
      SM.STRDECTopDec (strDec, NONE) => [strDec]
    | SM.STRDECTopDec (strDec, SOME topDec') => strDec :: topDecToStrDecList topDec'
    | _ => raise Fail "signatures and functors not yet supported"

  fun strDecToDec strDec =
    case A.syntax strDec of
      SM.DECStrDec dec => dec
    | _ => raise Fail "structures not yet supported"

  fun decToValBind dec =
    case A.syntax dec of
      SC.VALDec (tyVarSeq, valBind) => valBind
    | _ => raise Fail "currently only value bindings are supported"

  fun patToString pat =
    case A.syntax pat of
      SC.ATPat atPat => ( case A.syntax atPat of
        SC.IDAtPat (_, longVId) => LongVId.toString (A.syntax longVId)
      | _ => raise Fail "interesting atomic patterns not yet supported"
      )
    | _ => raise Fail "interesting patterns not yet supported"

  fun expToStringTree exp = Node ("unimplemented", [])

  fun valBindToStringTrees valBind =
    case A.syntax valBind of
      SC.PLAINValBind (pat, exp, NONE) =>
        [Node (patToString pat, [expToStringTree exp])]
    | SC.PLAINValBind (pat, exp, SOME valBind') =>
        Node (patToString pat, [expToStringTree exp])
        :: valBindToStringTrees valBind'
    | SC.RECValBind valBind' =>
        [Node ("rec", valBindToStringTrees valBind')]

  fun concatMap f = List.concat o map f

  fun stringTreeToAdjacencyList (Node (str, children)) =
    map (fn Node (str', _) => (str, str')) children @
    List.concat (map stringTreeToAdjacencyList children)

  (* want this to return i guess an adjacency list for right now *)
  (*
   * program : Parse.Program, which is the same thing as SyntaxProgram.Program
   * easy goal: write more readable code than whoever wrote HaMLet
   *
   * only supports declarations at the top level; no module stuff
   *)
  val compileGraphProgram : SP.Program -> (string * string) list =
    concatMap stringTreeToAdjacencyList o
    concatMap valBindToStringTrees o
    map decToValBind o
    map strDecToDec o
    concatMap topDecToStrDecList o
    programToTopDecList
end