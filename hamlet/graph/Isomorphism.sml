structure IsomorphismContext : sig
  type t
  val empty : t
  val fresh_id_pair : (LongVId.longId * LongVId.longId) * t -> t
  val iso : t -> LongVId.longId * LongVId.longId -> bool
end = 
struct
  val counter = ref 0
  fun fresh () = (counter := !counter + 1; !counter)

  structure M = BinaryMapFn(type ord_key = LongVId.longId val compare = LongVId.compare)
  type t = int M.map * int M.map

  val empty = (M.empty, M.empty)

  fun fresh_id_pair ((id1, id2), (m1, m2)) =
    let
      val s = fresh ()
    in
      (M.insert (m1, id1, s), M.insert (m2, id2, s))
    end

  fun iso (m1, m2) (id1, id2) =
    case (M.find (m1, id1), M.find (m2, id2)) of
      (SOME a, SOME b) => a = b
    | (NONE, NONE) => id1 = id2
    | _ => false
end

structure Isomorphism : sig
  val is_isomorphic : SyntaxProgram.Program -> bool
end = 
struct
  structure A = Annotation
  structure SP = SyntaxProgram
  structure SM = SyntaxModule
  structure SC = SyntaxCore
  structure IC = IsomorphismContext

  fun false_because str = (print (str ^ "\n"); false)
  fun none_because str = (print (str ^ "\n"); NONE)

  (* Isomorphism of special constants *)
  fun iso_sCon (sCon1, sCon2) = 
    SCon.toString (A.syntax sCon1) = SCon.toString (A.syntax sCon2)

  (* Isomorphism of patterns *)
  (* NOTE: non-boolean return type. Returns an optional list of variable pairs
    that have to be isomorphic for these patterns to be isomorphic (rudimentary
    unification *)
  fun iso_atPat (atPat1, atPat2) =
    case (A.syntax atPat1, A.syntax atPat2) of
      (SC.WILDCARDAtPat, SC.WILDCARDAtPat) => SOME []
    | (SC.SCONAtPat sCon1, SC.SCONAtPat sCon2) =>
        if iso_sCon (sCon1, sCon2)
        then SOME []
        else NONE
    | (SC.IDAtPat (op_opt1, id1), SC.IDAtPat (op_opt2, id2)) =>
        SOME [(A.syntax id1, A.syntax id2)]
    | (SC.RECORDAtPat patRow_opt1, SC.RECORDAtPat patRow_opt2) =>
        raise Fail "Tuples and records not supported."
    | (SC.PARAtPat pat1, SC.PARAtPat pat2) => iso_pat (pat1, pat2)
    | _ => NONE

  and iso_patRow (patRow1, patRow2) =
    case (A.syntax patRow1, A.syntax patRow2) of
      (SC.DOTSPatRow, SC.DOTSPatRow) => SOME []
    | ( SC.FIELDPatRow (lab1, pat1, patRow_opt1),
        SC.FIELDPatRow (lab2, pat2, patRow_opt2)  ) => (
        if A.syntax lab1 = A.syntax lab2
        then
          case iso_pat (pat1, pat2) of
            SOME unifications => (
              case (patRow_opt1, patRow_opt2) of
                (NONE, NONE) => SOME unifications
              | (SOME patRow1', SOME patRow2') => 
                Option.map
                  (fn u => unifications @ u)
                  (iso_patRow (patRow1', patRow2'))
              | _ => none_because "Tuples/records have different length."
            )
          | NONE => none_because "Patterns in tuple/record pattern don't match."
        else none_because ""
      )
    | _ => none_because "Tuples/records have different forms."

  (* TODO: make things like colon patterns not matter so much *)
  and iso_pat (pat1, pat2) =
    case (A.syntax pat1, A.syntax pat2) of
      (SC.ATPat atPat1, SC.ATPat atPat2) => iso_atPat (atPat1, atPat2)
    | (SC.CONPat (op_opt1, id1, atPat1), SC.CONPat (op_opt2, id2, atPat2)) =>
        if A.syntax id1 = A.syntax id2
        then iso_atPat (atPat1, atPat2)
        else NONE
    | (SC.COLONPat (pat1', ty1), SC.COLONPat (pat2', ty2)) =>
        iso_pat (pat1', pat2')
    | ( SC.ASPat (op_opt1, vId1, ty_opt1, pat1'),
        SC.ASPat (op_opt2, vId2, ty_opt2, pat2') ) =>
        raise Fail "As patterns not supported."
    | _ => NONE

  (* Isomorphism of expressions *)
  fun iso_expRow ctx (expRow1, expRow2) =
    case (A.syntax expRow1, A.syntax expRow2) of
      (SC.ExpRow (lab1, exp1, expRow_opt1), SC.ExpRow (lab2, exp2, expRow_opt2)) =>
      A.syntax lab1 = A.syntax lab2 andalso
      iso_exp ctx (exp1, exp2) andalso
      case (expRow_opt1, expRow_opt2) of
        (NONE, NONE) => true
      | (SOME expRow1', SOME expRow2') => iso_expRow ctx (expRow1', expRow2')
      | _ => false_because "Tuples/records have different lengths."

  and iso_atExp ctx (atExp1, atExp2) =
    case (A.syntax atExp1, A.syntax atExp2) of
      (SC.SCONAtExp sCon1, SC.SCONAtExp sCon2) => iso_sCon (sCon1, sCon2)
    | (SC.IDAtExp (op_opt1, id1), SC.IDAtExp (op_opt2, id2)) =>
        IC.iso ctx (A.syntax id1, A.syntax id2)
    | (SC.RECORDAtExp expRow_opt1, SC.RECORDAtExp expRow_opt2) => (
        case (expRow_opt1, expRow_opt2) of
          (NONE, NONE) => true
        | (SOME expRow1, SOME expRow2) => iso_expRow ctx (expRow1, expRow2)
        | _ => false_because "Tuples/records have different lengths (I think?)"        
      )
    | (SC.LETAtExp (dec1, exp1), SC.LETAtExp (dec2, exp2)) => (
        case iso_dec ctx (dec1, dec2) of
          SOME unifications =>
            iso_exp (foldl IC.fresh_id_pair ctx unifications) (exp1, exp2)
        | NONE => false_because "Declarations in let expression didn't match."
      )
    | (SC.PARAtExp exp1, SC.PARAtExp exp2) => iso_exp ctx (exp1, exp2)
    | _ => false_because "Different kinds of atomic expressions."

  and iso_mrule ctx (mrule1, mrule2) =
    case (A.syntax mrule1, A.syntax mrule2) of
      (SC.Mrule (pat1, exp1), SC.Mrule (pat2, exp2)) =>
      case (iso_pat (pat1, pat2)) of
        SOME unifications =>
          iso_exp (foldl IC.fresh_id_pair ctx unifications) (exp1, exp2)
      | NONE => false_because "Match patterns are different."

  and iso_match ctx (match1, match2) =
    case (A.syntax match1, A.syntax match2) of
      (SC.Match (mrule1, match_opt1), SC.Match (mrule2, match_opt2)) =>
      iso_mrule ctx (mrule1, mrule2) andalso
      case (match_opt1, match_opt2) of
        (NONE, NONE) => true
      | (SOME match1', SOME match2') => iso_match ctx (match1', match2')
      | _ => false_because "Different numbers of match clauses."

  and iso_exp ctx (exp1, exp2) =
    case (A.syntax exp1, A.syntax exp2) of
      (SC.ATExp atExp1, SC.ATExp atExp2) => iso_atExp ctx (atExp1, atExp2)
    | (SC.APPExp (exp1', atExp1), SC.APPExp (exp2', atExp2)) =>
        iso_exp ctx (exp1', exp2') andalso iso_atExp ctx (atExp1, atExp2)
    | (SC.COLONExp (exp1', ty1), SC.COLONExp (exp2', ty2)) =>
        iso_exp ctx (exp1', exp2')
    | (SC.FNExp match1, SC.FNExp match2) =>
        iso_match ctx (match1, match2)
    | (SC.HANDLEExp _, SC.HANDLEExp _) =>
        raise Fail "Handle expressions not supported."
    | (SC.RAISEExp _, SC.RAISEExp _) =>
        raise Fail "Raise expressions not supported."
    | _ => false_because "Different kinds of expressions."

  (* Isomorphism of valBinds *)
  (* NOTE: non-boolean return type. Returns an optional list of variable pairs
    that have to be isomorphic for these valBinds to be isomorphic *)
  and iso_valBind_help is_rec ctx (valBind1, valBind2) =
    case (A.syntax valBind1, A.syntax valBind2) of
      (SC.RECValBind valBind1', SC.RECValBind valBind2') =>
        iso_valBind_help true ctx (valBind1', valBind2')
    | ( SC.PLAINValBind (pat1, exp1, valBind_opt1),
        SC.PLAINValBind (pat2, exp2, valBind_opt2)  ) => (
        case iso_pat (pat1, pat2) of
          NONE => none_because "Patterns don't match."
        | SOME unifications =>
          let
            val ctx' =  if is_rec
                        then foldl IC.fresh_id_pair ctx unifications
                        else ctx
          in
            if iso_exp ctx' (exp1, exp2)
            then
              case (valBind_opt1, valBind_opt2) of
                (NONE, NONE) => SOME unifications
              | (SOME valBind1', SOME valBind2') =>
                  (* iso_valBind_help is_rec ctx (valBind1', valBind2') *)
                  raise Fail "Mutual recursion not supported."
              | _ => none_because ("One declaration was mutually recursive" ^
                                    " but the other was not.")
            else none_because "expressions in value binding don't match"
          end
        )
    | _ => none_because "One declaration was recursive but the other was not."
  and iso_valBind ctx = iso_valBind_help false ctx
 
  (* Isomorphism of declarations *)
  (* NOTE: non-boolean return type. Returns an optional list of variable pairs
    that have to be isomorphic for these declarations to be isomorphic *)
  and iso_dec ctx (dec1, dec2) =
    case (A.syntax dec1, A.syntax dec2) of
      (SC.VALDec (_, valBind1), SC.VALDec (_, valBind2)) =>
        iso_valBind ctx (valBind1, valBind2)
    | _ => raise Fail "Non-value declarations not supported."

  local
    fun programToTopDecList program =
      case A.syntax program of
        SP.Program (topDec, NONE) => [topDec]
      | SP.Program (topDec, SOME program') =>
          topDec :: programToTopDecList program'

    fun topDecToStrDecList topDec =
      case A.syntax topDec of
        SM.STRDECTopDec (strDec, NONE) => [strDec]
      | SM.STRDECTopDec (strDec, SOME topDec') =>
          strDec :: topDecToStrDecList topDec'
      | _ => raise Fail "Signatures and functors not supported."

    fun strDecToDec strDec =
      case A.syntax strDec of
        SM.DECStrDec dec => dec
      | _ => raise Fail "Structures not supported."

    fun firstTwo (a::b::_) = (a, b)
      | firstTwo _ = raise Fail "Fewer than two declarations present."

    fun concatMap f = List.concat o map f
  in
    val is_isomorphic = isSome o
                        iso_dec IC.empty o
                        firstTwo o
                        map strDecToDec o
                        concatMap topDecToStrDecList o
                        programToTopDecList
  end
end