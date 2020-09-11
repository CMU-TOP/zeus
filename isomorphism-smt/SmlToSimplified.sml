structure SmlToSimplified : SML_TO_SIMPLIFIED = 
struct

  structure A = Annotation
  structure SC = SyntaxCore
  structure S = SimplifiedSyntax

  structure M = BinaryMapFn(
    type ord_key = string
    val compare = String.compare
  )
  (* when we encounter an identifier, it's either:
    - a variable that was bound at some point, in which case it was associated with a
      symbol corresponding to that binding site
    - a constructor, in which case it either takes an argument or doesn't. *)
  datatype meaning = BoundVar of Symbol.t | Constructor of bool
  
  (* Each constructor either takes in no arguments (e.g. Leaf) or some
     arguments, (e.g. Node of Tree * Tree). In both constructors, the first
     string is the name of the constructor (Leaf and Node in the above examples)
     and in the Args constructor, SyntaxCore.Ty contains information regarding
     what types can be passed into the constrcutor *)
  datatype constructor_def = NoArgs of string | Args of string * SyntaxCore.Ty

  (* The first string is the name of the datatype. The string list is the list
     of polymorphic variable names (e.g. ('a, 'b) Node would have the string list
     ["'a", "'b"]). The constructor_def map is the map of all constructor
     definitions. *) 
  type datatype_def = string * string list * constructor_def M.map
  
  type datatype_def_map = datatype_def M.map
  
  type ctx = meaning M.map * datatype_def_map

  datatype phrase = datatype Annotation.phrase

  fun ` f annotated = f (A.syntax annotated)

  infixr 0 $
  fun f $ x = f x
  
  (* Print functions purely for debugging purposes *)
  fun symbol_typescheme_toString Symbol.Unknown = "Unknown"
    | symbol_typescheme_toString (Symbol.Known(t)) = 
        PrettyPrint.toString ((PPType.ppTypeScheme t), 100)
    | symbol_typescheme_toString (Symbol.Hardcoded(s)) = s

  fun meaning_map_toString meaning_map =
    let
      val meaning_map_list = M.listItemsi meaning_map 

      fun meaning_toString (key, Constructor(b)) = key ^ ": constructor"
        | meaning_toString (key, BoundVar(s)) = key ^ ": boundvar"

      fun meaning_list_toString [] = ""
        | meaning_list_toString (x::xs) = (meaning_toString x) ^ "\n" ^ (meaning_list_toString xs)
    in
      "Meaning map:\n\n" ^ (meaning_list_toString meaning_map_list)
    end

  fun print_constructor_map constructor_map =
    let
      val constructor_list = M.listItems constructor_map

      fun print_constructor_def (NoArgs(s)) = print s
        | print_constructor_def (Args(s, t)) = 
            (print (s ^ " of ");
            (PPCore.ppTy (TextIO.stdOut, 0, t)))

      fun print_constructor_list [] = ()
        | print_constructor_list (x::xs) = 
            (print_constructor_def x; print "\n"; print_constructor_list xs)
    in
      (print "Constructor map:\n\n";
      print_constructor_list constructor_list)
    end

  fun print_datatype_def_map datatype_def_map =
    let
      (* each element in list is of form: key * datatypename (same as key) * poly var list * constructor map *)
      val datatype_def_map_list = M.listItemsi datatype_def_map

      val constructor_map_list =
        List.map 
        (fn (key, (datatype_name, polyvar_list, constructor_map)) => 
          if (key = datatype_name) then (datatype_name, constructor_map)
          else raise Fail "datatype name invariant broken in datatype_def_map"
        ) datatype_def_map_list

      fun print_constructor_map_list [] = ()
        | print_constructor_map_list ((datatype_name, constructor_map)::xs) =
            (print (datatype_name ^ ":\n"); 
            print_constructor_map constructor_map; 
            print "\n\n"; 
            print_constructor_map_list xs)
    in
      print_constructor_map_list constructor_map_list
    end

  (* End of print functions purely for debugging purposes *)

  fun get_typescheme_from_exp (S.Const (_, t)) = t
    | get_typescheme_from_exp (S.Var (_, t)) = t
    | get_typescheme_from_exp (S.Record (_, t)) = t
    | get_typescheme_from_exp (S.Proj (_, _, t)) = t
    | get_typescheme_from_exp (S.Inj (_, _, t)) = t
    | get_typescheme_from_exp (S.Case (_, _, _, t)) = t
    | get_typescheme_from_exp (S.Lambda (_, _, t)) = t
    | get_typescheme_from_exp (S.App (_, _, t)) = t
    | get_typescheme_from_exp (S.Fix (_, _, t)) = t
    | get_typescheme_from_exp (S.Raise (_, t)) = t
    | get_typescheme_from_exp (S.Handle (_, _, t)) = t

  (* Type on left side of arrow type *) 
  fun get_hypothesis (StaticObjectsCore.Determined (t)) = get_hypothesis (!t)
    | get_hypothesis (StaticObjectsCore.FunType (hyp, con)) = hyp
    | get_hypothesis _ = raise Fail "Unexpected type format" 

  (* Type on right side of arrow type *)
  fun get_conclusion (StaticObjectsCore.Determined (t)) = get_conclusion (!t)
    | get_conclusion (StaticObjectsCore.FunType (hyp, con)) = con
    | get_conclusion _ = raise Fail "Unexpected type format"

  fun disambiguate_id_pat (ctx as (meaning_map, datatype_def_map)) (id, id_type) =
    case M.find (meaning_map, id) of
      SOME (Constructor false) =>
        (ctx, S.ConPat (id, S.RecordPat ([], Symbol.Hardcoded("unit")), id_type))
    | SOME (Constructor true) => raise Fail "Should be impossible"
    | (NONE | SOME (BoundVar _)) => 
      let 
        val s = Symbol.fresh (id, id_type)
        val meaning_map' = M.insert (meaning_map, id, BoundVar s)
      in 
        ((meaning_map', datatype_def_map), S.VarPat (s, id_type))
      end
    
  fun disambiguate_id_exp (meaning_map, datatype_def_map) (id, id_type) =
    case M.find (meaning_map, id) of
      SOME (Constructor false) => 
        S.Inj (id, S.Record ([], Symbol.Hardcoded("unit")), id_type)
    | SOME (Constructor true) =>
      let
        val Symbol.Known (tyvarlist, id_typescheme) = id_type

        val hypothesis_type = get_hypothesis(!id_typescheme)
        val conclusion_type = get_conclusion(!id_typescheme)

        val hypothesis_typescheme = Symbol.Known (tyvarlist, hypothesis_type)
        val conclusion_typescheme = Symbol.Known (tyvarlist, conclusion_type)

        val s = Symbol.fresh_nameless hypothesis_typescheme 
      in
        S.Lambda (s, S.Inj (id, S.Var (s, hypothesis_typescheme), conclusion_typescheme), id_type)
      end
    | SOME (BoundVar s) => 
        S.Var (s, id_type) (* id_type should be same as Symbol.get_type s *)
    | NONE => S.Var (Symbol.global (id, id_type), id_type)

  fun occurs x = (fn
    S.Const (c, t) => false
  | S.Var (y, t) => x = y
  | S.Record (rows, t) => List.exists (occurs x o #2) rows
  | S.Proj (e, l, t) => occurs x e
  | S.Inj (l, e, t) => occurs x e
  | S.Case (e, match, exhaustive, t) =>
      occurs x e orelse
      List.exists (occurs x o #2) match
  | S.Lambda (p, e, t) => occurs x e
  | S.App (e1, e2, t) => occurs x e1 orelse occurs x e2
  | S.Fix (p, e, t) => occurs x e
  | S.Raise (e, t) => occurs x e
  | S.Handle (e, (p, e'), t) => occurs x e orelse occurs x e'
  )
  
  fun simplify_base SCon.DEC = S.DEC
    | simplify_base SCon.HEX = S.HEX
  val simplify_sCon : SC.SCon -> S.const = `(fn
    SCon.INT (base, s) => S.INT (simplify_base base, s)
  | SCon.WORD (base, s) => S.WORD (simplify_base base, s)
  | SCon.STRING s => S.STRING s
  | SCon.CHAR s => S.CHAR s
  | SCon.REAL s => S.REAL s
  )

  val rec irrefutable = (fn
    S.WildcardPat _ => true
  | S.VarPat _ => true
  | S.RecordPat (rows, _) => List.all (irrefutable o #2) rows
  | S.AsPat (_, p, _) => irrefutable p
  | S.ConstPat _ => false
  | S.ConPat _ => false
  )

  fun simplify_patRow ctx = `(fn
    SC.DOTSPatRow => (ctx, [])
  | SC.FIELDPatRow (lab, pat, patRow_opt) =>
    let val (ctx', pat') = simplify_pat ctx pat
        val (ctx'', rest) = case patRow_opt of
          NONE => (ctx', [])
        | SOME patRow => simplify_patRow ctx' patRow
    in (ctx'', (Lab.toString (A.syntax lab), pat')::rest) end
  )

  and simplify_atPat ctx = fn (at_pat : SyntaxCore.AtPat) =>
  let
    val (at_pat' : SyntaxCore.AtPat')@@(annot : AnnotationCore.AtPat_attr Annotation.annotation) = at_pat
    val (valenv, typ) = AnnotationProgram.get (AnnotationProgram.elab annot)
    val typescheme = Symbol.Known (TyVarSet.listItems (StaticEnv.tyvarsVE valenv), typ)
  in
    case at_pat' of
      SC.WILDCARDAtPat => (ctx, S.WildcardPat typescheme)
    | SC.SCONAtPat sCon => (ctx, S.ConstPat (simplify_sCon sCon, typescheme))
    | SC.IDAtPat (_, longVId) =>
        disambiguate_id_pat ctx ((LongVId.toString (A.syntax longVId)), typescheme)
        (* Above uses typescheme rather than the type that can be scraped from 
        * longVId because longVId is general to the symbol, whereas typescheme uses
        * information from the other patterns (e.g. nil will be identified as
        * being of type 'a list in the longVId annotation but as int list in
        * typescheme if the overall pattern identifies it as such *) 
    | SC.RECORDAtPat NONE => (ctx, S.RecordPat ([], typescheme))
    | SC.RECORDAtPat (SOME patRow) =>
      let 
        val (ctx', patRow') = simplify_patRow ctx patRow
      in 
        (ctx', S.RecordPat (patRow', typescheme)) 
      end
    | SC.PARAtPat pat => simplify_pat ctx pat
  end

  and simplify_pat ctx = fn (pat : SyntaxCore.Pat) =>
  let
    val (pat' : SyntaxCore.Pat')@@(annot : AnnotationCore.Pat_attr Annotation.annotation) = pat
    val (valenv, typ) = AnnotationProgram.get (AnnotationProgram.elab annot)
    val typescheme = Symbol.Known (TyVarSet.listItems (StaticEnv.tyvarsVE valenv), typ)
  in
    case pat' of
      SC.ATPat atPat => simplify_atPat ctx atPat
    | SC.CONPat (_, longVId, atPat) =>
      let 
        val (ctx', pat) = simplify_atPat ctx atPat
      in 
        (ctx', S.ConPat (LongVId.toString (A.syntax longVId), pat, typescheme)) 
      end
    | SC.COLONPat (pat, _) => simplify_pat ctx pat
    | SC.ASPat (_, vId, _, pat) =>
      let
        val id = VId.toString (A.syntax vId)
        val s = Symbol.fresh (id, typescheme)

        val (meaning_map, datatype_def_map) = ctx

        val meaning_map' = M.insert (meaning_map, id, BoundVar s)
        val ctx' = (meaning_map', datatype_def_map)
        val (ctx'', pat') = simplify_pat ctx' pat
      in
        (ctx'', S.AsPat (s, pat', typescheme)) 
      end
  end 

  fun simplify_expRow ctx = `(fn
    SC.ExpRow (lab, exp, expRow_opt) =>
      (Lab.toString (A.syntax lab), simplify_exp ctx exp) :: (
      case expRow_opt of
        NONE => []
      | SOME expRow => simplify_expRow ctx expRow
      )
  )

  and simplify_atExp ctx = fn (at_exp : SyntaxCore.AtExp) =>
  let
    val (at_exp' : SyntaxCore.AtExp')@@(annot : AnnotationCore.AtExp_attr Annotation.annotation) = at_exp
    val typ = AnnotationProgram.get (AnnotationProgram.elab annot)
    val typescheme = Symbol.Known ([], typ)
  in
    case at_exp' of
      SC.SCONAtExp sCon => S.Const (simplify_sCon sCon, typescheme)
    | SC.IDAtExp (_, longVId) =>
        disambiguate_id_exp ctx ((LongVId.toString (A.syntax longVId)), typescheme)
    | SC.RECORDAtExp NONE => S.Record ([], typescheme)
    | SC.RECORDAtExp (SOME expRow) => S.Record (simplify_expRow ctx expRow, typescheme)
    | SC.LETAtExp (dec, in_exp) =>
      let val (ctx', pat_let_exps) = simplify_dec ctx dec in
        foldr
          (fn ((pat, let_exp), in_exp) => 
            S.Case (let_exp, [(pat, in_exp)], S.EXHAUSTIVE, typescheme))
          (simplify_exp ctx' in_exp)
          pat_let_exps
      end
    | SC.PARAtExp exp => simplify_exp ctx exp
  end
       
  and simplify_mrule ctx = fn (mrule : SyntaxCore.Mrule) =>
  let
    val (mrule' : SyntaxCore.Mrule')@@(annot : AnnotationCore.Mrule_attr Annotation.annotation) = mrule
  in
    case mrule' of
      SC.Mrule (pat, exp) =>
        let 
          val (ctx', pat) = simplify_pat ctx pat 
        in
          (pat, simplify_exp ctx' exp)
        end
  end

  and simplify_match_help ctx = fn (match : SyntaxCore.Match) =>
  let
    val (match' : SyntaxCore.Match')@@(annot : AnnotationCore.Match_attr Annotation.annotation) = match
    val typ = AnnotationProgram.get (AnnotationProgram.elab annot)

    val exhaustive_check_opt = AnnotationProgram.try(AnnotationCore.exhaustive annot)
    val exhaustive_check =
      case exhaustive_check_opt of
          SOME(check) => check
        | NONE => StaticObjectsCore.NonExhaustive
          (* I think NONE should only arise when simplify_match_help is called
          * recursively, in which case, #1 will be used on the result, rendering
          * whatever is put here irrelevant. But because I am uncertain, the
          * conservative thing to do is to say unless if I know that a match is
          * exhaustive, I will mark it as nonexhaustive *)
  in
    case match' of
      SC.Match (mrule, NONE) => ([simplify_mrule ctx mrule], exhaustive_check, typ)
    | SC.Match (mrule, SOME match) =>
        (simplify_mrule ctx mrule :: (#1 (simplify_match_help ctx match)), exhaustive_check, typ)
  end
  
  and simplify_match ctx match =
  case simplify_match_help ctx match of
    ([(S.VarPat (x, t), exp)], exhaustive_check, _) => (x, exp)
  | (cases, exhaustive_check, match_type) =>
    let
      val hypothesis_type = get_hypothesis (!match_type)
      val conclusion_type = get_conclusion (!match_type) 
     
      val hypothesis_typescheme = Symbol.Known ([], hypothesis_type)
      val conclusion_typescheme = Symbol.Known ([], conclusion_type)

      val s = Symbol.fresh_nameless hypothesis_typescheme

      val simplified_exhaustive =
        case exhaustive_check of
            StaticObjectsCore.Exhaustive => S.EXHAUSTIVE
          | StaticObjectsCore.NonExhaustive => S.NONEXHAUSTIVE 
    in 
      (s, S.Case (S.Var (s, hypothesis_typescheme), cases, simplified_exhaustive, conclusion_typescheme)) 
    end

  and simplify_exp ctx = fn (exp : SyntaxCore.Exp) =>
  let
    val (exp' : SyntaxCore.Exp')@@(annot : AnnotationCore.Exp_attr Annotation.annotation) = exp
    val typ = AnnotationProgram.get (AnnotationProgram.elab annot)
    val typescheme = Symbol.Known ([], typ)
  in
    case exp' of
      SC.ATExp atExp => simplify_atExp ctx atExp
    | SC.APPExp (exp, atExp) =>
        S.App (simplify_exp ctx exp, simplify_atExp ctx atExp, typescheme)
    | SC.COLONExp (exp, _) => simplify_exp ctx exp
    | SC.HANDLEExp (exp, match) =>
        S.Handle (simplify_exp ctx exp, simplify_match ctx match, typescheme)
    | SC.RAISEExp exp => S.Raise (simplify_exp ctx exp, typescheme)
    | SC.FNExp match =>
        let
          val (s, c) = simplify_match ctx match
        in
          S.Lambda (s, c, typescheme)
        end
  end

  and simplify_valBind_help is_rec ctx : SC.ValBind -> ctx * S.pat * S.exp = `(fn
    SC.RECValBind valBind => simplify_valBind_help true ctx valBind
  | SC.PLAINValBind (_, _, SOME _) => raise Fail "mutual declarations not yet supported"
  | SC.PLAINValBind (pat, exp, NONE) =>
    (* NOTE TO ANYONE READING THIS CODE: think thoroughly about scoping before
      making changes to this particular section of the code. There are
      subtleties in the scoping of fixed points that, if messed up, could make
      the isomorphism algorithm give wrong results or infinitely loop. *)
    let val (ctx', pat') = simplify_pat ctx pat in (
      ctx',
      pat',
      if is_rec then
        let
          val (ctx'', pat'') = simplify_pat ctx pat
          val x = case pat'' of
                    S.VarPat (x, t) => x
                  | _ => raise Fail "function name is too interesting"
          val exp' = simplify_exp ctx'' exp

          val typescheme = get_typescheme_from_exp exp'
        in
          if occurs x exp' then S.Fix (x, exp', typescheme) else exp'
        end
      else simplify_exp ctx exp
    ) end
  )
  and simplify_valBind ctx = simplify_valBind_help false ctx

  and simplify_dec (ctx as (meaning_map, datatype_def_map)) = 
  `(fn
      SC.VALDec (_, valBind) =>
      let val (ctx', pat, exp) = simplify_valBind ctx valBind
      in (ctx', [(pat, exp)]) end
    | SC.SEQDec (dec1, dec2) =>
      let val (ctx1, pat_let_exps1) = simplify_dec ctx dec1
          val (ctx2, pat_let_exps2) = simplify_dec ctx1 dec2
      in (ctx2, pat_let_exps1 @ pat_let_exps2) end
    | SC.DATATYPEDec (datbind'@@datbind_attr) =>
        let
          (* See hamlet/SyntaxCoreFn.sml for details on how information is stored *)
          val SyntaxCore.DatBind 
              (polymorphic_vars, datatype_name, 
               constructors, mut_rec_datatypes) = datbind'
               (* NOTE TO SELF: Zeus does not support mutually recursive
                  datatypes yet. Adding that will involve looking at
                  mut_rec_datatypes above and adding that information here *)
          
          val SyntaxCore.Seq(polymorphic_vars') = A.syntax polymorphic_vars

          val polymorphic_vars'_strings = 
            map (fn t => TyVar.toString (A.syntax t)) polymorphic_vars'

          val datatype_name' = TyCon.toString (A.syntax datatype_name)

          val constructors' = A.syntax constructors
          val SyntaxCore.ConBind
              (op_option, constructor_name,
               input_option, conbind_option) = constructors'

          val constructor_name' = VId.toString (A.syntax constructor_name)
          
          val constructor_def = 
            case input_option of
                 NONE => NoArgs constructor_name'
               | SOME(t) => Args (constructor_name', t)

          val constructor_def_map_initial = 
            M.singleton (constructor_name', constructor_def)

          fun create_constructor_def_map initial_map next_constructor =
            case next_constructor of
                 NONE => initial_map
               | SOME(constructor) =>
                  let
                    val SyntaxCore.ConBind
                        (op_option, constructor_name,
                         input_option, conbind_option) = (A.syntax constructor)

                    val constructor_name' = VId.toString (A.syntax constructor_name)

                    val constructor_def =
                      case input_option of
                           NONE => NoArgs constructor_name'
                         | SOME(t) => Args (constructor_name', t)

                    val updated_map = 
                      M.insert (initial_map, constructor_name', constructor_def)
                  in
                    create_constructor_def_map updated_map conbind_option 
                  end

          val constructor_def_map = 
            create_constructor_def_map constructor_def_map_initial conbind_option

          (* Add new constructors to meaning map *)
          val constructor_def_list = M.listItems constructor_def_map

          fun update_meaning_map meaning_map [] = meaning_map
            | update_meaning_map meaning_map (NoArgs(s)::constructor_def_list_rest) =
                (if (M.inDomain (meaning_map, s)) then 
                  (if (M.find (meaning_map, s) = SOME(Constructor false)) then
                    update_meaning_map meaning_map constructor_def_list_rest
                  else raise Fail ("Disallowed constructor name: " ^ s))
                else
                  let
                    val meaning_map' = M.insert (meaning_map, s, Constructor false)
                  in
                    update_meaning_map meaning_map' constructor_def_list_rest
                  end)
            | update_meaning_map meaning_map (Args(s, t)::constructor_def_list_rest) =
                (if (M.inDomain (meaning_map, s)) then 
                  (if (M.find (meaning_map, s) = SOME(Constructor true)) then
                    update_meaning_map meaning_map constructor_def_list_rest
                  else raise Fail "Disallowed constructor name")
                else
                  let
                    val meaning_map' = M.insert (meaning_map, s, Constructor true)
                  in
                    update_meaning_map meaning_map' constructor_def_list_rest
                  end)

          val meaning_map' = update_meaning_map meaning_map constructor_def_list

          (* Update datatype_def_map *)
          val new_datatype_def = 
            (datatype_name', polymorphic_vars'_strings, constructor_def_map)
          
          val datatype_def_map' =
            if (not(M.inDomain (datatype_def_map, datatype_name'))) then 
              M.insert (datatype_def_map, datatype_name', new_datatype_def)
           else raise Fail "Disallowed datatype names"
        in
          ((meaning_map', datatype_def_map'), [])
        end
      | (SC.EMPTYDec | SC.TYPEDec _ | SC.DATATYPE2Dec _ |
        SC.ABSTYPEDec _ | SC.EXCEPTIONDec _ |
        SC.OPENDec _ | SC.LOCALDec _) => (ctx, []) 
  )

  val initial_meaning_map = M.map Constructor $ foldl M.insert' M.empty [
    ("true", false),
    ("false", false),
    ("nil", false),
    ("::", true),
    ("LESS", false),
    ("EQUAL", false),
    ("GREATER", false),
    ("NONE", false),
    ("SOME", true),

    ("Empty", false),
    ("Bind", false),
    ("Match", false),
    ("Fail", true),
    ("Option", false),
    ("Subscript", false),
    ("Chr", false),
    ("Div", false)
  ]

  val initial_datatype_def_map = M.empty

  val initial_ctx = (initial_meaning_map, initial_datatype_def_map)
 
  fun extract_from_decs decs id =
  let 
    val (ctx', pat_let_exps) =
    foldl
    (fn (dec, (ctx, pat_let_exps)) =>
      let val (ctx', this_pat_let_exps) = simplify_dec ctx dec
      in (ctx', pat_let_exps @ this_pat_let_exps) end
    )
    (initial_ctx, [])
    decs

    val (meaning_map, datatype_def_map) = ctx'
  in (foldr
      (fn ((pat, let_exp), in_exp) =>
        if irrefutable pat
        (* S.EXHAUSTIVE because in this case the pat is irrefutable *)
        then S.Case (let_exp, [(pat, in_exp)], S.EXHAUSTIVE, get_typescheme_from_exp in_exp)
        else in_exp
        (* NOTE: this gives some justification
          for keeping variables at binding sites unique:
          since variables bound in refutable patterns get
          thrown out, expressions using that variable get
          a meaningless symbol, which isn't as bad as possibly
          capturing a different variable
         *)
      )
      (case M.find (meaning_map, id) of
          SOME (BoundVar symbol) => (S.Var (symbol, Symbol.get_type symbol))
        | SOME (Constructor _) => raise Fail ("symbol " ^ id ^ " is a constructor")
        | NONE => raise Fail ("symbol " ^ id ^ " not bound in declarations")
      )
      pat_let_exps, datatype_def_map)
  end
end
