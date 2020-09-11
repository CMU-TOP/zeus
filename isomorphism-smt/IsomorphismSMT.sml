structure Isomorphism : sig
  val is_isomorphic : 
    (SimplifiedSyntax.exp * SmlToSimplified.datatype_def_map) *
    (SimplifiedSyntax.exp * SmlToSimplified.datatype_def_map) -> bool
end = 
struct
  (*
    Generating an SMTLib program based on constraints introduced by
    two SML expressions being equivalent.
  *)

  structure A = Annotation  
  structure S = SimplifiedSyntax
  open SMTLib
  
  local val And' = And in
    fun And [x] = x
      | And l = And' l
  end

  structure Dict = BinaryMapFn(
    type ord_key = string
    val compare = String.compare
  )

  datatype constructor_def = datatype SmlToSimplified.constructor_def
  datatype phrase = datatype Annotation.phrase

  (* A typescheme used only for insertion in locations where a typescheme is
  * required but unobtainable and unused *)
  val dummy_typescheme = Symbol.Unknown

  (* Print functions purely for debugging purposes *)
    fun print_polymorphic_vars'_strings [] = ()
      | print_polymorphic_vars'_strings (s::rest) =
          (print s; print "\n"; print_polymorphic_vars'_strings rest)

    fun print_constructor_def constructor_def =
      case constructor_def of
           SmlToSimplified.NoArgs(s) => print ("NoArgs(" ^ s ^ ")\n")
         | SmlToSimplified.Args(s, t) => 
             (print ("Args(" ^ s ^ ", ");
             PPCore.ppTy (TextIO.stdOut, 0, t))

    fun print_constructor_def_map constructor_def_map =
      SmlToSimplified.M.foldl 
        (fn (constructor_def, ()) => 
          print_constructor_def constructor_def) () constructor_def_map

    fun print_datatype_def_map datatype_def_map =
      SmlToSimplified.M.foldl
        (fn (datatype_def, ()) =>
          let
            val (datatype_name, polymorphic_vars'_strings, 
                 constructor_def_map) = datatype_def
          in
            print "datatype: ";
            print datatype_name;
            print "\npolymorphic vars: ";
            print_polymorphic_vars'_strings polymorphic_vars'_strings;
            print "\nconstructors: ";
            print_constructor_def_map constructor_def_map
          end
        ) () datatype_def_map


  fun symbol_typescheme_toString Symbol.Unknown = "Unknown"
    | symbol_typescheme_toString (Symbol.Known(t)) = 
        PrettyPrint.toString ((PPType.ppTypeScheme t), 100)
    | symbol_typescheme_toString (Symbol.Hardcoded(s)) = s
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


  fun is_isomorphic ((program1, datatype_def_map1), 
                     (program2, datatype_def_map2)) =
  let
    fun exists_shared_names_helper [] = false
      | exists_shared_names_helper ((name1, _, _)::xs) =
          List.exists (fn (name2, _, _) => name1=name2) xs
          orelse exists_shared_names_helper xs

    fun exists_shared_names datatype_map =
      exists_shared_names_helper (SmlToSimplified.M.listItems datatype_map)

    val () = 
      if (exists_shared_names datatype_def_map1 orelse 
          exists_shared_names datatype_def_map2)
      then raise Fail "Disallowed datatype names"
      else ()

    fun constructors_equal (_, NoArgs s1) (_, NoArgs s2) _ _ = (s1 = s2)
      | constructors_equal (_, NoArgs s1) (_, Args _) _ _ = false
      | constructors_equal (_, Args _) (_, NoArgs s2) _ _ = false
      | constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.VARTy(tyvar1)@@_)) 
                           (polymorphic_vars_list2, Args (s2, SyntaxCore.VARTy(tyvar2)@@_)) 
                           _ _ =
          let
            val t1 = TyVar.toString(A.syntax tyvar1)
            val t2 = TyVar.toString(A.syntax tyvar2)

            fun add_index L =
              let
                fun add_index_helper (nil,  _) = nil
                  | add_index_helper (h::tl,i) = (h,i) :: add_index_helper (tl, 1+i)
              in
                add_index_helper (L, 0)
              end

            val indexed_polymorphic_vars_list1 = add_index polymorphic_vars_list1
            val indexed_polymorphic_vars_list2 = add_index polymorphic_vars_list2

            val t1_index =
              case (List.find (fn (t, i) => t1 = t) indexed_polymorphic_vars_list1) of
                   NONE => ~1
                 | SOME(_, i) => i
            
            val t2_index = 
              case (List.find (fn (t, i) => t2 = t) indexed_polymorphic_vars_list2) of
                   NONE => ~1
                 | SOME(_, i) => i
          in
            s1 = s2 andalso t1_index = t2_index andalso t1_index >= 0
          end
      | constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.RECORDTy(tyrow1_opt)@@annot1))
                           (polymorphic_vars_list2, Args (s2, SyntaxCore.RECORDTy(tyrow2_opt)@@annot2))
                           shared_datatypes cur_datatype_name =
          let
            val tyrow1 = 
              case tyrow1_opt of
                   NONE => raise Fail "I don't think this is possible"
                 | SOME(t@@_) => t

            val tyrow2 = 
              case tyrow2_opt of
                   NONE => raise Fail "I don't think this is possible"
                 | SOME(t@@_) => t

            val SyntaxCore.TyRow(_, curty1, next1_opt) = tyrow1
            val SyntaxCore.TyRow(_, curty2, next2_opt) = tyrow2
          in
            s1 = s2 andalso
            constructors_equal (polymorphic_vars_list1, Args (s1, curty1))
                               (polymorphic_vars_list2, Args (s2, curty2))
                               shared_datatypes cur_datatype_name
            andalso
            (case (next1_opt, next2_opt) of
                 (NONE, NONE) => true
               | (SOME(_), NONE) => false
               | (NONE, SOME(_)) => false
               | (SOME(next1), SOME(next2)) =>
                 constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.RECORDTy(SOME next1)@@annot1))
                                    (polymorphic_vars_list2, Args (s2, SyntaxCore.RECORDTy(SOME next2)@@annot2))
                                    shared_datatypes cur_datatype_name
                                    (* NOTE: annot1 and annot2 are not the appropriate annotations 
                                       for next1 and next2. I only include them in this manner
                                       as a means of forcing constructors_equal to type check (this
                                       does not cause a problem so long as constructors_equal never 
                                       uses the annotations) *)
            )
          end
      | constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.PARTy(ty1)@@_))
                           (polymorphic_vars_list2, Args (s2, SyntaxCore.PARTy(ty2)@@_))
                           shared_datatypes cur_datatype_name =
          s1 = s2 andalso
          constructors_equal (polymorphic_vars_list1, Args (s1, ty1))
                             (polymorphic_vars_list2, Args (s2, ty2))
                             shared_datatypes cur_datatype_name
      | constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.ARROWTy(left1, right1)@@_))
                           (polymorphic_vars_list2, Args (s2, SyntaxCore.ARROWTy(left2, right2)@@_)) 
                           shared_datatypes cur_datatype_name =
          s1 = s2 andalso
          constructors_equal (polymorphic_vars_list1, Args (s1, left1))
                             (polymorphic_vars_list2, Args (s2, left2))
                             shared_datatypes cur_datatype_name
          andalso
          constructors_equal (polymorphic_vars_list1, Args (s1, right1))
                             (polymorphic_vars_list2, Args (s2, right2))
                             shared_datatypes cur_datatype_name
      | constructors_equal (polymorphic_vars_list1, Args (s1, SyntaxCore.CONTy(tyseq1, longtycon1)@@_))
                           (polymorphic_vars_list2, Args (s2, SyntaxCore.CONTy(tyseq2, longtycon2)@@_)) 
                           shared_datatypes cur_datatype_name =
          let
            val (SyntaxCore.Seq tylist1)@@_ = tyseq1
            val (SyntaxCore.Seq tylist2)@@_ = tyseq2

            val combined_ty_list = 
              List.tabulate 
                ((Int.min (List.length tylist1, List.length tylist2)),
                (fn i => (List.nth (tylist1, i), List.nth (tylist2, i))))

            fun is_in_shared_datatypes_helper s nil = false
              | is_in_shared_datatypes_helper s (x::xs) =
                  (s = x) orelse (is_in_shared_datatypes_helper s xs)

            fun is_in_shared_datatypes s =
              s = cur_datatype_name orelse
              is_in_shared_datatypes_helper s shared_datatypes
          in
            s1 = s2 andalso
            (LongTyCon.compare (A.syntax longtycon1, A.syntax longtycon2) = EQUAL)
            andalso (is_in_shared_datatypes (LongTyCon.toString (A.syntax longtycon1)))
            andalso (List.length tylist1 = List.length tylist2)
            andalso
            (List.all 
              (fn (ty1, ty2) =>
                constructors_equal (polymorphic_vars_list1, Args(s1, ty1))
                                   (polymorphic_vars_list2, Args(s2, ty2))
                                   shared_datatypes cur_datatype_name
              ) combined_ty_list
            )
          end
      | constructors_equal _ _ _ _ = false
    
    fun datatypes_equal (name1, polymorphic_vars_list1, constructor_map1)
                        (name2, polymorphic_vars_list2, constructor_map2) 
                        shared_datatypes =
      (name1 = name2 
      andalso 
      SmlToSimplified.M.numItems constructor_map1 = SmlToSimplified.M.numItems constructor_map2 
      andalso
      SmlToSimplified.M.all 
        (fn constructor1 => 
          SmlToSimplified.M.exists
            (fn constructor2 => 
              constructors_equal (polymorphic_vars_list1, constructor1) 
                                 (polymorphic_vars_list2, constructor2)
                                  shared_datatypes name1
            ) constructor_map2
        ) constructor_map1
      )

    val built_in_datatypes =
      ["int", "char", "bool", "string", "real", "unit", "list", "option", "order"]

    val shared_datatypes =
      SmlToSimplified.M.foldl (fn (cur_def, shared_datatypes) =>
        let
          val matchexists =
            SmlToSimplified.M.exists 
              (fn possible_match =>
                datatypes_equal cur_def possible_match shared_datatypes
              ) datatype_def_map2
        in
          if (matchexists) then
            let
              val (cur_datatype_name, _, _) = cur_def
            in
              cur_datatype_name :: shared_datatypes
            end
          else shared_datatypes
        end
      ) built_in_datatypes datatype_def_map1

    val unshared_datatypes1 =
      List.map (fn (name, _, _) => name ^ "-1")
        (SmlToSimplified.M.listItems 
          (SmlToSimplified.M.filter (fn (name1, _, _) =>
            List.exists (fn name2 => name1=name2) shared_datatypes)
              datatype_def_map1))
       
    val unshared_datatypes2 =
      List.map (fn (name, _, _) => name ^ "-2")
        (SmlToSimplified.M.listItems
          (SmlToSimplified.M.filter (fn (name1, _, _) =>
            List.exists (fn name2 => name1=name2) shared_datatypes)
              datatype_def_map2))

    (* Get shared and unshared constructors for injection labels *)
    fun get_constructors_list datatype_def_map =
      SmlToSimplified.M.foldl
        (fn (datatype_def, L)=>
          let
            val (_, _, constructor_def_map) = datatype_def 

            fun get_constructor_name (SmlToSimplified.NoArgs(s)) = s
              | get_constructor_name (SmlToSimplified.Args(s, _)) = s

            val new_constructors =
              SmlToSimplified.M.foldl
                (fn (constructor_def, L2) =>
                  (get_constructor_name constructor_def)::L2
                ) [] constructor_def_map
          in
            new_constructors @ L
          end
        ) [] datatype_def_map
      
    val shared_constructors = 
      get_constructors_list
        (SmlToSimplified.M.filter 
          (fn (name, _, _) => 
            List.exists (fn name2 => name = name2) shared_datatypes
          ) datatype_def_map1)
    
    val unshared_constructors1 =
      get_constructors_list
        (SmlToSimplified.M.filter
          (fn (name, _, _) =>
            not (List.exists (fn name2 => name = name2) shared_datatypes)
          ) datatype_def_map1)

    val unshared_constructors2 =
      get_constructors_list
        (SmlToSimplified.M.filter
          (fn (name, _, _) =>
            not (List.exists (fn name2 => name = name2) shared_datatypes)
          ) datatype_def_map2)
   
    (* Adding shared and unshared datatypes to the list of injection labels *)
    val shared_constructors_labels =
      List.map (fn name => (name, "prog-inj-" ^ name)) shared_constructors

    val unshared_constructors1_labels =
      List.map (fn name => (name, "prog-inj-" ^ name ^ "-1")) unshared_constructors1

    val unshared_constructors2_labels =
      List.map (fn name => (name, "proj-inj-" ^ name ^ "-2")) unshared_constructors2

    (* hardcode a short list of injection labels to begin with *)
    val inj_labels = foldr Dict.insert' Dict.empty [
      ("true", "prog-inj-true"),
      ("false", "prog-inj-false"),
      ("nil", "prog-inj-nil"),
      ("::", "prog-inj-cons"),
      ("LESS", "prog-inj-less"),
      ("EQUAL", "prog-inj-equal"),
      ("GREATER", "prog-inj-greater"),
      ("NONE", "prog-inj-none"),
      ("SOME", "prog-inj-some"),
      ("Empty", "prog-inj-empty"),
      ("Bind", "prog-inj-bind"),
      ("Match", "prog-inj-match"),
      ("Fail", "prog-inj-fail"),
      ("Option", "prog-inj-option"),
      ("Subscript", "prog-inj-subscript"),
      ("Chr", "prog-inj-chr"),
      ("Div", "prog-inj-div")
    ]

    val inj_labels = foldr Dict.insert' inj_labels shared_constructors_labels
    val inj_labels = foldr Dict.insert' inj_labels unshared_constructors1_labels
    val inj_labels = foldr Dict.insert' inj_labels unshared_constructors2_labels
      
    (*
      name = name of prog function
      f = name of SMTLib built-in function
    *)
    fun define_term_comparison name f =
      DefineFun (name, [("x", "Dyn")], "Dyn",
        IfThenElse (
          App (f, [App ("fst", [Ident "x"]), App ("snd", [Ident "x"])]),
          App ("prog-inj", [Ident "prog-inj-true", Ident "prog-unit"]),
          App ("prog-inj", [Ident "prog-inj-false", Ident "prog-unit"])
        )
      )

    (*
      name = name of prog function
      f = name of SMTLib built-in function
    *)
    fun define_arithmetic_comparison name f = 
      DefineFun (name, [("x", "Dyn")], "Dyn",
        IfThenElse (
          App (f, [
            App ("value", [App ("fst", [Ident "x"])]),
            App ("value", [App ("snd", [Ident "x"])])
          ]),
          App ("prog-inj", [Ident "prog-inj-true", Ident "prog-unit"]),
          App ("prog-inj", [Ident "prog-inj-false", Ident "prog-unit"])
        )
      )

    (*
      name = name of prog function
      f = name of SMTLib built-in function
    *)
    fun define_arithmetic_binop name f =
      DefineFun (name, [("x", "Dyn")], "Dyn",
        App ("prog-const", [
          App (f, [
            App ("value", [App ("fst", [Ident "x"])]),
            App ("value", [App ("snd", [Ident "x"])])
          ])
        ])
      )

    (* mapping from SML function name to name of prog function *)
    (* names of prog functions are arbitrary but must match the preamble *)
    val atomic_functions = foldr Dict.insert' Dict.empty [
      ("=", "prog-eq"),
      ("<>", "prog-neq"),
      ("<", "prog-lt"),
      ("<=", "prog-lte"),
      (">", "prog-gt"),
      (">=", "prog-gte"),
      ("+", "prog-plus"),
      ("-", "prog-minus"),
      ("*", "prog-times")
    ]

    (*
      preamble is a bunch of declarations to insert at the top of the file,
      for every invocation of the algorithm no matter what.
      preamble = AST nodes
    *)
    val preamble : command list = [
      DeclareDatatype ("InjLabel",
        map (fn l => (l, [])) (Dict.listItems inj_labels)
      ),
      DeclareDatatype ("Dyn", [
        (* Constants (we currently only support integer constants) *)
        ("prog-const", [("value", "Int")]),
        ("prog-str", [("str_value", "String")]),
        (* Records (for now just hardcode a few tuple sizes) *)
        ("prog-unit", []),
        ("prog-tuple2", [("fst", "Dyn"), ("snd", "Dyn")]),
        ("prog-tuple3", [("fst3", "Dyn"), ("snd3", "Dyn"), ("third3", "Dyn")]),
        ("prog-tuple4", [("fst4", "Dyn"), ("snd4", "Dyn"), ("third4", "Dyn"), ("fourth4", "Dyn")]),
        ("prog-tuple5", [("fst5", "Dyn"), ("snd5", "Dyn"), ("third5", "Dyn"),
                         ("fourth5", "Dyn"), ("fifth5", "Dyn")]),
        ("prog-tuple6", [("fst6", "Dyn"), ("snd6", "Dyn"), ("third6", "Dyn"),
                         ("fourth6", "Dyn"), ("fifth6", "Dyn"), ("sixth6", "Dyn")]),
        ("prog-tuple7", [("fst7", "Dyn"), ("snd7", "Dyn"), ("third7", "Dyn"),
                         ("fourth7", "Dyn"), ("fifth7", "Dyn"), ("sixth7", "Dyn"),
                         ("seventh7", "Dyn")]),
        ("prog-tuple8", [("fst8", "Dyn"), ("snd8", "Dyn"), ("third8", "Dyn"),
                         ("fourth8", "Dyn"), ("fifth8", "Dyn"), ("sixth8", "Dyn"),
                         ("seventh8", "Dyn"), ("eighth8", "Dyn")]),
        (* injections *)
        ("prog-inj", [("lab", "InjLabel"), ("val", "Dyn")])
      ]),
      (* variables *)
      DeclareFun ("prog-var", ["Int"], "Dyn"),
      DeclareFun ("prog-var-int", ["Int"], "Dyn"),
      DeclareFun ("prog-var-str", ["Int"], "Dyn"),
      (* Projections *)
      DefineFun ("prog-proj-1", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple2", Ident "e"),
          App ("fst", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple3", Ident "e"),
            App ("fst3", [Ident "e"]),
            IfThenElse (
              Test ("prog-tuple4", Ident "e"),
              App ("fst4", [Ident "e"]),
              IfThenElse (
                Test ("prog-tuple5", Ident "e"),
                App ("fst5", [Ident "e"]),
                IfThenElse (
                  Test ("prog-tuple6", Ident "e"),
                  App ("fst6", [Ident "e"]),
                  IfThenElse (
                    Test ("prog-tuple7", Ident "e"),
                    App ("fst7", [Ident "e"]),
                    App ("fst8", [Ident "e"])
                  )
                )
              )
            )
          )
        )
      ),
      DefineFun ("prog-proj-2", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple2", Ident "e"),
          App ("snd", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple3", Ident "e"),
            App ("snd3", [Ident "e"]),
            IfThenElse (
              Test ("prog-tuple4", Ident "e"),
              App ("snd4", [Ident "e"]),
              IfThenElse (
                Test ("prog-tuple5", Ident "e"),
                App ("snd5", [Ident "e"]),
                IfThenElse (
                  Test ("prog-tuple6", Ident "e"),
                  App ("snd6", [Ident "e"]),
                  IfThenElse (
                    Test ("prog-tuple7", Ident "e"),
                    App ("snd7", [Ident "e"]),
                    App ("snd8", [Ident "e"])
                  )
                )
              )
            )
          )
        )
      ),
      DefineFun ("prog-proj-3", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple3", Ident "e"),
          App ("third3", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple4", Ident "e"),
            App ("third4", [Ident "e"]),
            IfThenElse (
              Test ("prog-tuple5", Ident "e"),
              App ("third5", [Ident "e"]),
              IfThenElse (
                Test ("prog-tuple6", Ident "e"),
                App ("third6", [Ident "e"]),
                IfThenElse (
                  Test ("prog-tuple7", Ident "e"),
                  App ("third7", [Ident "e"]),
                  App ("third8", [Ident "e"])
                )
              )
            )
          )
        )
      ),
      DefineFun ("prog-proj-4", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple4", Ident "e"),
          App ("fourth4", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple5", Ident "e"),
            App ("fourth5", [Ident "e"]),
            IfThenElse (
              Test ("prog-tuple6", Ident "e"),
              App ("fourth6", [Ident "e"]),
              IfThenElse (
                Test ("prog-tuple7", Ident "e"),
                App ("fourth7", [Ident "e"]),
                App ("fourth8", [Ident "e"])
              )
            )
          )
        )
      ),
      DefineFun ("prog-proj-5", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple5", Ident "e"),
          App ("fifth5", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple6", Ident "e"),
            App ("fifth6", [Ident "e"]), 
            IfThenElse (
              Test ("prog-tuple7", Ident "e"),
              App ("fifth7", [Ident "e"]),
              App ("fifth8", [Ident "e"])
            )
          )
        )
      ),
      DefineFun ("prog-proj-6", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple6", Ident "e"),
          App ("sixth6", [Ident "e"]),
          IfThenElse (
            Test ("prog-tuple7", Ident "e"),
            App ("sixth7", [Ident "e"]),
            App ("sixth8", [Ident "e"])
          )
        )
      ),
      DefineFun ("prog-proj-7", [("e", "Dyn")], "Dyn",
        IfThenElse (
          Test ("prog-tuple7", Ident "e"),
          App ("seventh7", [Ident "e"]),
          App ("seventh8", [Ident "e"])
        )
      ),
      DefineFun ("prog-proj-8", [("e", "Dyn")], "Dyn",
        App ("eighth8", [Ident "e"])
      ),
      (* special treatment of certain functions *)
      define_term_comparison "prog-eq" "=",
      define_term_comparison "prog-neq" "distinct",
      define_arithmetic_comparison "prog-lt" "<",
      define_arithmetic_comparison "prog-lte" "<=",
      define_arithmetic_comparison "prog-gt" ">",
      define_arithmetic_comparison "prog-gte" ">=",
      define_arithmetic_binop "prog-plus" "+",
      define_arithmetic_binop "prog-minus" "-",
      define_arithmetic_binop "prog-times" "*"
    ]

    val prog_var_int_definition =
      ForAll ([("i", "Int")], 
      Exists ([("j", "Int")],
      Equals [App ("prog-var-int", [Ident "i"]),
              App ("prog-const", [Ident "j"])]
      ))

    val prog_var_str_definition =
      ForAll ([("i", "Int")],
      Exists ([("s", "String")],
      Equals [App ("prog-var-str", [Ident "i"]),
              App ("prog-str", [Ident "s"])]
      ))

    fun bound_in x = fn
      S.WildcardPat t => false
    | S.VarPat (y, t) => y = x
    | S.RecordPat (rows, t) => List.exists (bound_in x o #2) rows
    | S.AsPat (y, p, t) => y = x orelse bound_in x p
    | S.ConstPat _ => false
    | S.ConPat (_, p, t) => bound_in x p

    (* subst: Takes every occurrence of x and replaces it with e *)
    fun subst (x, e) = fn
      S.Const (c, t) => S.Const (c, t)
    | S.Var (y, t) => if y = x then e else S.Var (y, t)
    | S.Record (rows, t) => 
        S.Record (map (fn (l, ei) => (l, subst (x, e) ei)) rows, t)
    | S.Proj (e', l, t) => S.Proj (subst (x, e) e', l, t)
    | S.Inj (l, e', t) => S.Inj (l, subst (x, e) e', t)
    | S.Case (e', match, is_exhaustive, t) => S.Case (
        subst (x, e) e',
        map (fn (pi, ei) => (pi, if bound_in x pi then ei else subst (x, e) ei)) match,
        is_exhaustive, t 
      )
    | S.Lambda (x', e', t) =>
        if x' = x
        then S.Lambda (x', e', t)
        else S.Lambda (x', subst (x, e) e', t)
    | S.App (e1, e2, t) => S.App (subst (x, e) e1, subst (x, e) e2, t)
    | S.Fix (x', e', t) =>
        if x' = x
        then S.Fix (x', e', t)
        else S.Fix (x', subst (x, e) e', t)
    | S.Raise (e', t) => S.Raise (subst (x, e) e', t)
    | S.Handle (e', (x', e''), t) => S.Handle (
        subst (x, e) e',
        (if x' = x
        then (x', e'')
        else (x', subst (x, e) e'')),
        t 
      )

    infix 1 >>=
    fun NONE >>= _ = NONE
      | (SOME x) >>= f = f x

    (*
      if the pattern is irrefutable,
      returns a function which takes the expression being bound to the pattern
      and returns a function to transform the expression under the binder.
    *)
    val rec is_irrefutable : S.pat -> (S.exp -> S.exp -> S.exp) option = fn
      S.WildcardPat t => SOME (Fn.const Fn.id)
    | S.VarPat (x, t) => SOME (fn e => subst (x, e))
    | S.RecordPat (rows, t) =>
      let
        val (labels, pats) = ListPair.unzip rows
        val transformer_opts = map is_irrefutable pats
      in
        if List.all isSome transformer_opts then SOME (fn e => fn e' =>
          foldr (fn ((li, fi), e'') =>
            fi (S.Proj (e, li, dummy_typescheme)) e''
          ) e' (ListPair.zip (labels, map valOf transformer_opts))
        ) else NONE
      end
    | S.AsPat (x, p, t) =>
      is_irrefutable p >>= (fn f =>
        SOME (fn e => subst (x, e) o f e)
      )
    | S.ConstPat _ => NONE
    | S.ConPat _ => NONE

    val rec freshen = fn
      (S.WildcardPat t, e) => (S.WildcardPat t, e)
    | (S.VarPat (x, t), e) =>
      let 
        val y = Symbol.fresh (Symbol.name x, Symbol.get_type x) 
      in
        (S.VarPat (y, t), subst (x, S.Var (y, t)) e)
      end
    | (S.RecordPat (rows, t), e) =>
      let
        val (rows', e') = foldr (fn ((li, pi), (rows', e')) =>
          let val (pi', e'') = freshen (pi, e') in
            ((li, pi')::rows', e'')
          end
        ) ([], e) rows
      in
        (S.RecordPat (rows', t), e')
      end
    | (S.AsPat (x, p, t), e) =>
      let
        val y = Symbol.fresh (Symbol.name x, Symbol.get_type x)
        val (p', e') = freshen (p, e)
      in
        (S.AsPat (y, p', t), subst (x, S.Var (y, Symbol.get_type y)) e')
      end
    | (S.ConstPat (c, t), e) => (S.ConstPat (c, t), e)
    | (S.ConPat (li, p, t), e) =>
      let val (p', e') = freshen (p, e) in
        (S.ConPat (li, p', t), e')
      end

    val rec whnf_step = fn
      S.App (S.Lambda (x, body, t_lambda), arg, t_app) =>
          SOME (subst (x, arg) body)
    | S.App (e1, e2, t) =>
        Option.map
          (fn e1' => S.App (e1', e2, t))
          (whnf_step e1)
    | S.Proj (S.Record (rows, t_record), l, t_proj) =>
        Option.map #2 (List.find (fn (l', _) => l'=l) rows)
    | S.Proj (e, l, t) => Option.map (fn e' => S.Proj (e', l, t)) (whnf_step e)
    | S.Case (e, match as (p, e')::_, is_exhaustive, t) => (
        case is_irrefutable p of
          SOME f => SOME (f e e')
        | NONE => Option.map (fn e => S.Case (e, match, is_exhaustive, t)) (whnf_step e)
      )
    | _ => NONE

    fun whnf e =
      case whnf_step e of
        NONE => e
      | SOME e' => whnf e'

    (* Determines whether two patterns are equivalent up to a substitution of free
       variables (this isn't a test of alpha equivalence, just pattern equivalence) *) 
    val rec equiv_patterns = fn
      (S.AsPat (x, x_pat, x_t), S.AsPat (y, y_pat, y_t)) => equiv_patterns (x_pat, y_pat)
    | (S.AsPat (x, x_pat, x_t), y_pat) => equiv_patterns (x_pat, y_pat)
    | (x_pat, S.AsPat(y, y_pat, y_t)) => equiv_patterns (x_pat, y_pat)
    | (S.WildcardPat t1, S.WildcardPat t2) => true
    | (S.WildcardPat wildcard_t, S.VarPat (y, y_t)) => true
    | (S.VarPat (x, x_t), S.WildcardPat wildcard_t) => true
    | (S.VarPat (x, x_t), S.VarPat (y, y_t)) => true
    | (S.RecordPat (rows1, t1), S.RecordPat (rows2, t2)) =>
        (case (rows1, rows2) of
             (nil, nil) => true
           | (x::xs, nil) => false
           | (nil, y::ys) => false
           | ((xl, xp)::xs, (yl, yp)::ys) => equiv_patterns (xp, yp) andalso 
                                             equiv_patterns (
                                              S.RecordPat (xs, dummy_typescheme), 
                                              S.RecordPat (ys, dummy_typescheme)))
    | (S.ConstPat (c1, t1), S.ConstPat (c2, t2)) => c1 = c2
    | (S.ConPat (x_li, x_pat, x_t), S.ConPat (y_li, y_pat, y_t)) =>
        x_li = y_li andalso equiv_patterns (x_pat, y_pat)
    | _ => false

    fun freshen_together (match1, nil) = (map freshen match1, nil)
      | freshen_together (nil, match2) = (nil, map freshen match2)
      | freshen_together (match1 as (p1, e1)::restmatch1, match2 as (p2, e2)::restmatch2) =
          let
            (* freshen_together_helper freshens (p1, e1) and (p2, e2) together if
               and only if p1 and p2 are equivalent. *)
            fun freshen_together_helper ((p1, e1), (p2, e2)) =
            let
              val (e1, e2) = (whnf e1, whnf e2)
            in
              case (p1, p2) of
                  (S.AsPat (x, x_pat, x_t), S.AsPat (y, y_pat, y_t)) =>
                    if (equiv_patterns (x_pat, y_pat)) then
                      let
                        val z = Symbol.fresh (Symbol.name x, Symbol.get_type x)
                        val e1' = subst (x, S.Var (z, Symbol.get_type z)) e1
                        val e2' = subst (y, S.Var (z, Symbol.get_type z)) e2
                        val ((x_pat', e1''), (y_pat', e2'')) =
                          freshen_together_helper ((x_pat, e1'), (y_pat, e2')) 
                      in
                        ((S.AsPat (z, x_pat', Symbol.get_type z), e1''), 
                         (S.AsPat (z, y_pat', Symbol.get_type z), e2''))
                      end
                    else (freshen (p1, e1), freshen (p2, e2))
                | (S.AsPat (x, x_pat, x_t), y_pat) =>
                    if (equiv_patterns (x_pat, y_pat)) then
                      let
                        val x' = Symbol.fresh (Symbol.name x, Symbol.get_type x)
                        val e1' = subst (x, S.Var (x', Symbol.get_type x')) e1
                        val ((x_pat', e1''), (y_pat', e2')) =
                          freshen_together_helper ((x_pat, e1'), (y_pat, e2))
                      in
                        ((S.AsPat (x', x_pat', Symbol.get_type x'), e1''), (y_pat', e2'))
                      end
                    else (freshen (p1, e1), freshen (p2, e2))
                | (x_pat, S.AsPat (y, y_pat, y_t)) =>
                    if (equiv_patterns (x_pat, y_pat)) then
                      let
                        val y' = Symbol.fresh (Symbol.name y, Symbol.get_type y)
                        val e2' = subst (y, S.Var (y', Symbol.get_type y')) e2
                        val ((x_pat', e1'), (y_pat', e2'')) =
                          freshen_together_helper ((x_pat, e1), (y_pat, e2'))
                      in
                        ((x_pat', e1'), (S.AsPat (y', y_pat', Symbol.get_type y'), e2''))
                      end
                    else (freshen (p1, e1), freshen (p2, e2))
                | (S.VarPat (x, x_t), S.VarPat (y, y_t)) =>
                    let 
                      val z = Symbol.fresh (Symbol.name x, Symbol.get_type x) 
                    in
                      ((S.VarPat (z, Symbol.get_type z), 
                        subst (x, S.Var (z, Symbol.get_type z)) e1), 
                       (S.VarPat (z, Symbol.get_type z), 
                        subst (y, S.Var (z, Symbol.get_type z)) e2))
                    end
                | (S.VarPat (x, x_t), S.WildcardPat wildcard_t) =>
                     let 
                       val z = Symbol.fresh (Symbol.name x, Symbol.get_type x)
                     in
                       ((S.VarPat (z, Symbol.get_type z), 
                         subst (x, S.Var (z, Symbol.get_type z)) e1),
                        (S.VarPat (z, Symbol.get_type z), e2))
                     end
                 | (S.WildcardPat wildcard_t, S.VarPat (x, x_t)) =>
                     let
                       val z = Symbol.fresh (Symbol.name x, Symbol.get_type x)
                     in
                       ((S.VarPat (z, Symbol.get_type z), e1),
                        (S.VarPat (z, Symbol.get_type z), 
                         subst (x, S.Var (z, Symbol.get_type z)) e2))
                     end
                 | (S.WildcardPat t1, S.WildcardPat t2) =>
                     let
                       val z = Symbol.fresh_nameless t1
                     in
                       ((S.VarPat (z, t1), e1), 
                        (S.VarPat (z, t1), e2))
                     end
                | (S.RecordPat (rows1, t1), S.RecordPat (rows2, t2)) =>
                    if (equiv_patterns (p1, p2)) then
                      let
                        fun freshen_rows_together ((rows1, e1), (rows2, e2)) =
                          case (rows1, rows2) of
                                (nil, nil) => 
                                  ((S.RecordPat (nil, t1), e1), 
                                   (S.RecordPat (nil, t2), e2))
                              | ((s1, x)::rest1, (s2, y)::rest2) =>
                                  let
                                    val ((x', e1'), (y', e2')) =
                                      freshen_together_helper ((x, e1), (y, e2))

                                    val ((S.RecordPat (rest1', _), final_e1), 
                                         (S.RecordPat (rest2', _), final_e2)) =
                                      freshen_rows_together ((rest1, e1'), (rest2, e2'))
                                  in
                                    ((S.RecordPat ((s1, x')::rest1', t1), final_e1), 
                                     (S.RecordPat ((s2, y')::rest2', t2), final_e2))
                                  end
                              | _ => raise Fail "Unreachable" 
                                    (* because p1 and p2 are equivalent patterns,
                                       the previous cases are actually exhaustive *)
                      in
                        freshen_rows_together ((rows1, e1), (rows2, e2))
                      end
                    else (freshen (p1, e1), freshen (p2, e2))
                | (S.ConstPat (c1, t1), S.ConstPat (c2, t2)) => 
                    ((S.ConstPat (c1, t1), e1), (S.ConstPat (c2, t2), e2))
                | (S.ConPat (x_li, x_pat, x_t), S.ConPat (y_li, y_pat, y_t)) =>
                    if (x_li = y_li andalso equiv_patterns (x_pat, y_pat)) then
                      let
                        val ((x_pat', e1'), (y_pat', e2')) =
                          freshen_together_helper ((x_pat, e1), (y_pat, e2))
                      in
                        ((S.ConPat (x_li, x_pat', x_t), e1'), 
                         (S.ConPat (y_li, y_pat', y_t), e2'))
                      end
                    else (freshen (p1, e1), freshen (p2, e2))
                | _ => (freshen (p1, e1), freshen (p2, e2)) 
            end
            
            val ((p1', e1'), (p2', e2')) = freshen_together_helper ((p1, e1), (p2, e2))
          in
            (* Checking whether patterns are equivalent, rather than equal,
               because one might be an AsPat pattern while the other isn't, and
               still have been freshened together. (p1, e1) and (p2, e2) should
               have been freshened together if and only if p1 and p2 are equivalent *)
            if (equiv_patterns (p1', p2')) then
              let
                val (restmatch1', restmatch2') = freshen_together (restmatch1, restmatch2)
              in
                ((p1', e1')::restmatch1', (p2', e2')::restmatch2')
              end
            else ((p1', e1')::(map freshen restmatch1), (p2', e2')::(map freshen restmatch2))
          end

    fun alpha_equiv_helper (S.Lambda (s1, e1, t1), S.Lambda(s2, e2, t2)) =
          let
            val z = Symbol.fresh_nameless (Symbol.get_type s1)
            val e1' = subst (s1, S.Var (z, Symbol.get_type z)) e1
            val e2' = subst (s2, S.Var (z, Symbol.get_type z)) e2
          in
            alpha_equiv (e1', e2')
          end
      | alpha_equiv_helper (S.Const (c1, t1), S.Const (c2, t2)) = c1 = c2
      | alpha_equiv_helper (S.Var (x, x_t), S.Var (y, y_t)) = x = y
      | alpha_equiv_helper (S.Record (rows1, t1), S.Record (rows2, t2)) =
          (case (rows1, rows2) of
               (nil, nil) => true
             | (x::xs, nil) => false
             | (nil, y::ys) => false
             | ((xl, xe)::xs, (yl, ye)::ys) => alpha_equiv (xe, ye) andalso
                                               alpha_equiv (S.Record (xs, dummy_typescheme), 
                                                            S.Record (ys, dummy_typescheme)))
      | alpha_equiv_helper (S.Proj (xe, xl, x_t), S.Proj (ye, yl, y_t)) =
          xl = yl andalso alpha_equiv (xe, ye)
      | alpha_equiv_helper (S.Inj (xl, xe, x_t), S.Inj (yl, ye, y_t)) =
          xl = yl andalso alpha_equiv (xe, ye)
      | alpha_equiv_helper (S.Case (xe, xmatch, x_exhaustive, x_t), S.Case (ye, ymatch, y_exhaustive, y_t)) =
          if (alpha_equiv (xe, ye)) then
            let
              val (xmatch', ymatch') = freshen_together (xmatch, ymatch)
              
              val x_pattern_list = map (fn (p, e) => p) xmatch'
              val y_pattern_list = map (fn (p, e) => p) ymatch'

              fun check_lists (nil, nil) = true
                | check_lists (x::xs, nil) = false
                | check_lists (nil, y::ys) = false
                | check_lists (x::xs, y::ys) =
                    equiv_patterns(x, y) andalso check_lists (xs, ys)

              val pattern_lists_match = check_lists (x_pattern_list, y_pattern_list)

              val x_expression_list = map (fn (p, e) => ("dummy string", e)) xmatch'
              val y_expression_list = map (fn (p, e) => ("dummy string", e)) ymatch'
            in
              pattern_lists_match andalso
              alpha_equiv (S.Record (x_expression_list, dummy_typescheme), 
                           S.Record (y_expression_list, dummy_typescheme))
              (* To check whether xmatch and ymatch are alpha equivalent given
                 that xe and ye are alpha equivalent, I first check that each of
                 the patterns in the two lists match one to one with each other.
                 Then, if that check passes, I check whether each of the
                 expressions that the overall case expressions can output also
                 match one to one. I perform this second check using something of
                 a hack where I put each of the expressions in a record and then
                 use alpha_equiv to determine whether the two records are
                 alpha equivalent. This works because when alpha_equiv is given
                 two records, it iterates through each element in both records and
                 confirms that each pair of elements in the two records are alpha
                 equivalent to one another *) 
            end
          else false
      | alpha_equiv_helper (S.App (x1, x2, x_t), S.App (y1, y2, y_t)) =
          alpha_equiv (x1, y1) andalso alpha_equiv (x2, y2)
      | alpha_equiv_helper (S.Fix (s1, e1, t1), S.Fix (s2, e2, t2)) =
          let
            val z = Symbol.fresh_nameless t1
            val e1' = subst (s1, S.Var (z, Symbol.get_type z)) e1
            val e2' = subst (s2, S.Var (z, Symbol.get_type z)) e2
          in
            alpha_equiv (e1', e2')
          end
      | alpha_equiv_helper (S.Raise (e1, t1), S.Raise (e2, t2)) = alpha_equiv (e1, e2)
      | alpha_equiv_helper (S.Handle (e1, (s1, e1'), t1), S.Handle (e2, (s2, e2'), t2)) =
          alpha_equiv (e1, e2) andalso s1 = s2 andalso alpha_equiv (e1', e2')
      | alpha_equiv_helper _ = false

    and alpha_equiv (e1, e2) = alpha_equiv_helper (whnf e1, whnf e2)

    (* subst_app_var: Takes every application of fn_symbol and args and replaces it with x *)
    fun subst_app_var_helper (x, fn_symbol, args) = fn
        S.Const (c, t) => S.Const (c, t)
      | S.Var (y, t) => S.Var (y, t)
      | S.Record (rows, t) => 
          S.Record (map (fn (l, ei) => (l, subst_app_var (x, fn_symbol, args) ei)) rows, t)
      | S.Proj (e', l, t) => S.Proj (subst_app_var (x, fn_symbol, args) e', l, t)
      | S.Inj (l, e', t) => S.Inj (l, subst_app_var (x, fn_symbol, args) e', t)
      | S.Case (e', match, is_exhaustive, t) =>
          S.Case (
            subst_app_var (x, fn_symbol, args) e',
            map (fn (pi, ei) => (pi, subst_app_var (x, fn_symbol, args) ei)) match,
            is_exhaustive, t 
          )
      | S.Lambda (x', e', t) =>
          if x' = fn_symbol
          then S.Lambda (x', e', t)
          else S.Lambda (x', subst_app_var (x, fn_symbol, args) e', t) 
      | S.App (S.Var (s, var_t), e', app_t) =>
          if (s = fn_symbol andalso e' = args) then x
          else 
            S.App (S.Var (s, var_t), subst_app_var (x, fn_symbol, args) e', app_t)
      | S.App (e1, e2, t) => 
          S.App (subst_app_var (x, fn_symbol, args) e1, subst_app_var (x, fn_symbol, args) e2, t)
      | S.Fix (x', e', t) =>
          if x' = fn_symbol
          then S.Fix (x', e', t)
          else S.Fix (x', subst_app_var (x, fn_symbol, args) e', t)
      | S.Raise (e', t) => S.Raise (subst_app_var (x, fn_symbol, args) e', t)
      | S.Handle (e', (x', e''), t) => S.Handle (
          subst_app_var (x, fn_symbol, args) e',
          (if x' = fn_symbol
          then (x', e'')
          else (x', subst_app_var (x, fn_symbol, args) e'')),
          t 
        )
    and subst_app_var (x, fn_symbol, args) = 
      (fn e => subst_app_var_helper (x, fn_symbol, args) (whnf e))
           
    (* subst_app_fix: Takes every application of S.Fix(s, e) and args and replaces it with x *)
    fun subst_app_fix_helper (x, s, e, args) = (fn
        S.Const (c, t) => S.Const (c, t)
      | S.Var (y, t) => S.Var (y, t)
      | S.Record (rows, t) => 
          S.Record (map (fn (l, ei) => (l, subst_app_fix (x, s, e, args) ei)) rows, t)
      | S.Proj (e', l, t) => S.Proj (subst_app_fix (x, s, e, args) e', l, t)
      | S.Inj (l, e', t) => S.Inj (l, subst_app_fix (x, s, e, args) e', t)
      | S.Case (e', match, is_exhaustive, t) =>
          S.Case (
            subst_app_fix (x, s, e, args) e',
            map (fn (pi, ei) => (pi, subst_app_fix (x, s, e, args) ei)) match,
            is_exhaustive, t 
          )
      | S.Lambda (x', e', t) => 
          S.Lambda (x', subst_app_fix (x, s, e, args) e', t)
      | S.App (S.Fix (s', e', t_fix), e'', t_app) =>
          if (alpha_equiv (e, subst (s', S.Var (s, Symbol.get_type s)) e') andalso e'' = args) then x
          else S.App (S.Fix (s', subst_app_fix (x, s, e, args) e', t_fix),
                      subst_app_fix (x, s, e, args) e'', t_app)
      | S.App (e1, e2, t) =>
          S.App (subst_app_fix (x, s, e, args) e1, subst_app_fix (x, s, e, args) e2, t)
      | S.Fix (x', e', t) => S.Fix (x', subst_app_fix (x, s, e, args) e', t)
      | S.Raise (e', t) => S.Raise (subst_app_fix (x, s, e, args) e', t)
      | S.Handle (e', (x', e''), t) => S.Handle (
          subst_app_fix (x, s, e, args) e',
          (x', subst_app_fix (x, s, e, args) e''),
          t 
        ))
    and subst_app_fix (x, s, e, args) = 
      (fn e' => subst_app_fix_helper (x, s, e, args) (whnf e'))
    
    fun symbol_term s =
      let
        val typ = 
          case (Symbol.get_type s) of
               Symbol.Unknown => "Unknown"
             | Symbol.Hardcoded(typ_str) => typ_str
             | Symbol.Known(typ') =>
                  PrettyPrint.toString (PPType.ppTypeScheme typ', 100)
      in
        if (typ = "int") then
          App ("prog-var-int", [Const (Symbol.guid s)])
        else if (typ = "string") then
          App ("prog-var-str", [Const (Symbol.guid s)])
        else
          App ("prog-var", [Const (Symbol.guid s)])
      end

    (*
      an expression is atomic (we've also called this "constrainable")
      if it's simple enough to give to the SMT solver.
      i.e. we don't need to use knowledge of SML semantics to break it down
      further; it's simple enough to check using naive equality of symbols.
      is_atomic should return an SMTLib term of sort Dyn.
    *)
    val rec is_atomic : S.exp -> term option = fn
      S.Const (S.INT (_, c), t) =>
        SOME (App ("prog-const", [Const (valOf (Int.fromString c))]))
    | S.Const ((S.STRING s, t) | (S.CHAR s, t)) =>
        SOME (App ("prog-str", [String s]))
    | S.Const ((S.WORD _, t) | (S.REAL _, t)) =>
        raise Fail "Unsupported constant used"
    | S.Var (s, t) => SOME (symbol_term s)
    | S.Record (rows, t) => (
        case rows of
          [] => SOME (Ident "prog-unit")
        | [("1", e1), ("2", e2)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
              SOME (App ("prog-tuple2", [e1_term, e2_term]))
            ))
        | [("1", e1), ("2", e2), ("3", e3)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
              SOME (App ("prog-tuple3", [e1_term, e2_term, e3_term]))
            )))
        | [("1", e1), ("2", e2), ("3", e3), ("4", e4)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
            is_atomic e4 >>= (fn e4_term =>
              SOME (App ("prog-tuple4", [e1_term, e2_term, e3_term, e4_term]))
            ))))
        | [("1", e1), ("2", e2), ("3", e3), ("4", e4), ("5", e5)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
            is_atomic e4 >>= (fn e4_term =>
            is_atomic e5 >>= (fn e5_term =>
              SOME (App ("prog-tuple5", [e1_term, e2_term, e3_term, e4_term, e5_term]))
            )))))
        | [("1", e1), ("2", e2), ("3", e3), ("4", e4), ("5", e5), ("6", e6)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
            is_atomic e4 >>= (fn e4_term =>
            is_atomic e5 >>= (fn e5_term =>
            is_atomic e6 >>= (fn e6_term =>
              SOME (App ("prog-tuple6", [e1_term, e2_term, e3_term, e4_term, e5_term, e6_term]))
            ))))))
        | [("1", e1), ("2", e2), ("3", e3), ("4", e4), ("5", e5), ("6", e6), ("7", e7)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
            is_atomic e4 >>= (fn e4_term =>
            is_atomic e5 >>= (fn e5_term =>
            is_atomic e6 >>= (fn e6_term =>
            is_atomic e7 >>= (fn e7_term =>
              SOME (App ("prog-tuple7", [e1_term, e2_term, e3_term, e4_term,
                                         e5_term, e6_term, e7_term]))
            )))))))
        | [("1", e1), ("2", e2), ("3", e3), ("4", e4), ("5", e5), ("6", e6), ("7", e7), ("8", e8)] =>
            is_atomic e1 >>= (fn e1_term =>
            is_atomic e2 >>= (fn e2_term =>
            is_atomic e3 >>= (fn e3_term =>
            is_atomic e4 >>= (fn e4_term =>
            is_atomic e5 >>= (fn e5_term =>
            is_atomic e6 >>= (fn e6_term =>
            is_atomic e7 >>= (fn e7_term =>
            is_atomic e8 >>= (fn e8_term =>
              SOME (App ("prog-tuple8", [e1_term, e2_term, e3_term, e4_term,
                                         e5_term, e6_term, e7_term, e8_term]))
            ))))))))
        | _ => (
            List.app (fn (l, _) => print (l ^ ", ")) rows;
            print "\n";
            raise Fail "unsupported tuple situation tbh"
          )
      )
    | S.Proj (e, l, t) => is_atomic e >>= (fn e_term =>
        SOME (App ("prog-proj-" ^ l, [e_term]))
      )
    | S.Inj (l, e, t) => is_atomic e >>= (fn e_term =>
        SOME (App ("prog-inj", [Ident (valOf (Dict.find (inj_labels, l))), e_term]))
      )
    | S.App (S.Var (s, var_t), e, app_t) =>
      if Symbol.is_global s then
        Dict.find (atomic_functions, Symbol.name s) >>= (fn s_atom =>
        is_atomic e >>= (fn e_term =>
          SOME (App (s_atom, [e_term]))
        ))
      else NONE
    | S.App _ => NONE
    | ( S.Case _
      | S.Lambda _
      | S.Fix _
      | S.Raise _
      | S.Handle _) => NONE

    (* Returns:
      - a list of assertions about term equalities (sort Bool)
      - term of sort Dyn representing the pattern
    *)
    val rec pat_to_term : S.pat -> term list * term = fn
      S.WildcardPat t => pat_to_term (S.VarPat (Symbol.fresh_nameless t, t))
    | S.VarPat (x, t) => ([], symbol_term x)
    | S.RecordPat (rows, t) => (
        case rows of
          [] => ([], Ident "prog-unit")
        | [("1", p1), ("2", p2)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
          in
            (
              p1_eqs @ p2_eqs,
              App ("prog-tuple2", [p1_term, p2_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs,
              App ("prog-tuple3", [p1_term, p2_term, p3_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3), ("4", p4)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
            val (p4_eqs, p4_term) = pat_to_term p4
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs @ p4_eqs,
              App ("prog-tuple4", [p1_term, p2_term, p3_term, p4_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3), ("4", p4), ("5", p5)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
            val (p4_eqs, p4_term) = pat_to_term p4
            val (p5_eqs, p5_term) = pat_to_term p5
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs @ p4_eqs @ p5_eqs,
              App ("prog-tuple5", [p1_term, p2_term, p3_term, p4_term, p5_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3), ("4", p4), ("5", p5), ("6", p6)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
            val (p4_eqs, p4_term) = pat_to_term p4
            val (p5_eqs, p5_term) = pat_to_term p5
            val (p6_eqs, p6_term) = pat_to_term p6
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs @ p4_eqs @ p5_eqs @ p6_eqs,
              App ("prog-tuple6", [p1_term, p2_term, p3_term, p4_term, p5_term, p6_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3), ("4", p4), ("5", p5), ("6", p6), ("7", p7)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
            val (p4_eqs, p4_term) = pat_to_term p4
            val (p5_eqs, p5_term) = pat_to_term p5
            val (p6_eqs, p6_term) = pat_to_term p6
            val (p7_eqs, p7_term) = pat_to_term p7
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs @ p4_eqs @ p5_eqs @ p6_eqs @ p7_eqs,
              App ("prog-tuple7", [p1_term, p2_term, p3_term, p4_term, 
                                   p5_term, p6_term, p7_term])
            )
          end
        | [("1", p1), ("2", p2), ("3", p3), ("4", p4), ("5", p5), ("6", p6), ("7", p7), ("8", p8)] =>
          let
            val (p1_eqs, p1_term) = pat_to_term p1
            val (p2_eqs, p2_term) = pat_to_term p2
            val (p3_eqs, p3_term) = pat_to_term p3
            val (p4_eqs, p4_term) = pat_to_term p4
            val (p5_eqs, p5_term) = pat_to_term p5
            val (p6_eqs, p6_term) = pat_to_term p6
            val (p7_eqs, p7_term) = pat_to_term p7
            val (p8_eqs, p8_term) = pat_to_term p8
          in
            (
              p1_eqs @ p2_eqs @ p3_eqs @ p4_eqs @ p5_eqs @ p6_eqs @ p7_eqs @ p8_eqs,
              App ("prog-tuple8", [p1_term, p2_term, p3_term, p4_term, 
                                   p5_term, p6_term, p7_term, p8_term])
            )
          end
        | _ => (
            List.app (fn (l, _) => print (l ^ ", ")) rows;
            print "\n";
            raise Fail "unsupported tuple situation tbh"
          )
      )
    | S.AsPat (x, p, t) =>
      let
        val (p_eqs, p_term) = pat_to_term p
        val (_, x_term) = pat_to_term (S.VarPat (x, Symbol.get_type x))
        val x_p_eq = Equals [x_term, p_term]
      in
        (x_p_eq::p_eqs, p_term)
      end
    | S.ConstPat (S.INT (_, c), t) =>
        ([], App ("prog-const", [Const (valOf (Int.fromString c))]))
    | S.ConstPat ((S.STRING s, t) | (S.CHAR s, t)) =>
        ([], App ("prog-str", [String s]))
    | S.ConstPat ((S.WORD (_, c), t) | (S.REAL c, t)) =>
        raise Fail "unsupported constant situation tbh"
    | S.ConPat (l, p, t) =>
      let
        val (p_eqs, p_term) = pat_to_term p
      in
        (p_eqs, App ("prog-inj", [Ident (valOf (Dict.find (inj_labels, l))), p_term]))
      end
    fun generate_term (e1, e2) = (*
      print "\n====================================================\n";
      print (SimplifiedUtils.toString (whnf e1));
      print "\n\n";
      print (SimplifiedUtils.toString (whnf e2));
      print "\n====================================================\n"; *)
      generate_term' (e1, e2)
    (* *)

    and generate_term' (expression1, expression2) =
    let
      val (exp1, exp2) = (whnf expression1, whnf expression2)
    in
      case (is_atomic exp1, is_atomic exp2) of
        (SOME exp1_term, SOME exp2_term) => Equals [exp1_term, exp2_term]
      | _ => (* at least one of them isn't constrainable; decompose *)
      case (exp1, exp2) of
        (S.Record (rows1, t1), S.Record (rows2, t2)) => (And (
          ListPair.mapEq (fn ((l1, e1), (l2, e2)) =>
            if l1 = l2 then generate_term (e1, e2) else False
          ) (rows1, rows2)
        ) handle UnequalLengths => False)
      | (S.Inj (l1, e1, t1), S.Inj (l2, e2, t2)) => 
          if l1 = l2 then generate_term (e1, e2) else False
      | (S.Case(e1, match1, is_exhaustive1, t1), S.Case(e2, match2, is_exhaustive2, t2)) =>
          if(is_exhaustive1 = S.NONEXHAUSTIVE orelse is_exhaustive2 = S.NONEXHAUSTIVE) 
            then False
          else if (alpha_equiv (e1, e2)) then (case is_atomic e1 of
          SOME e1_term =>
            let
              val (match1', match2') = freshen_together(match1, match2)

              fun add_index L =
                let
                  fun add_index_helper (nil,  _) = nil
                    | add_index_helper (h::tl,i) = (h,i) :: add_index_helper (tl, 1+i)
                in
                  add_index_helper (L, 0)
                end
 
              val match1'withindices = add_index match1'
              val match2'withindices = add_index match2'
            in
              And (List.concat 
              (map (fn ((p1i, e1i), index1) =>
                (map (fn ((p2i, e2i), index2) =>
                  let
                    val (p1i_eqs, p1i_term) = pat_to_term p1i
                    val (p2i_eqs, p2i_term) = pat_to_term p2i

                    val prevmatch1'withindices = List.filter (fn (_, i) => i < index1) match1'withindices
                    val prevmatch2'withindices = List.filter (fn (_, i) => i < index2) match2'withindices

                    val nopreviousmatchesterm1 =
                      case prevmatch1'withindices of
                            nil => True
                          | _ =>
                              And (map (fn ((prev_p1i, prev_e1i), previndex) =>
                                let
                                  val (prev_p1i_eqs, prev_p1i_term) = pat_to_term prev_p1i
                                in
                                  Not (And (Equals [e1_term, prev_p1i_term] :: prev_p1i_eqs))
                                end
                              ) prevmatch1'withindices)

                    val nopreviousmatchesterm2 =
                      case prevmatch2'withindices of
                            nil => True
                          | _ =>
                              And (map (fn ((prev_p2i, prev_e2i), previndex) =>
                                let
                                  val (prev_p2i_eqs, prev_p2i_term) = pat_to_term prev_p2i
                                in
                                  Not (And (Equals [e1_term, prev_p2i_term] :: prev_p2i_eqs))
                                end
                              ) prevmatch2'withindices)
                  in
                    Implies [
                      And (
                      [ nopreviousmatchesterm1, nopreviousmatchesterm2,
                        Equals [e1_term, p1i_term], Equals [e1_term, p2i_term]] @ p1i_eqs @ p2i_eqs),
                      generate_term (e1i, e2i)
                    ]
                  end
                ) match2'withindices)
              ) match1'withindices))
            end
        | NONE => (case (match1, match2) of
            ([(S.VarPat (x, x_t), e1')], [(S.VarPat (y, y_t), e2')]) =>
              generate_term ((subst (x, e1) e1'), (subst (y, e2) e2'))
          | ([(S.VarPat (x, x_t), e1')], [(S.WildcardPat wildcard_t, e2')]) =>
              generate_term ((subst (x, e1) e1'), e2')
          | ([(S.WildcardPat wildcard_t, e1')], [(S.VarPat (y, y_t), e2')]) =>
              generate_term (e1', (subst (y, e2) e2'))
          | ([(S.WildcardPat t1, e1')], [(S.WildcardPat t2, e2')]) =>
              generate_term (e1', e2')
          | _ => 
              let
                val typescheme_e1 = get_typescheme_from_exp e1
                val x = S.Var (Symbol.fresh_nameless typescheme_e1, typescheme_e1)
              in
                (* Don't need to check whether e1 and e2 are equal because we
                   know they are *)
                generate_term (S.Case (x, match1, is_exhaustive1, t1), S.Case (x, match2, is_exhaustive2, t2))
              end
          ) 
        )
          else generate_term'_case(exp1, exp2)
      | ( (exp1 as S.Case (e1, match1, is_exhaustive1, t1), exp2)
        | (exp2, exp1 as S.Case (e1, match1, is_exhaustive1, t1)) ) => 
            if(is_exhaustive1 = S.NONEXHAUSTIVE) then False
            else generate_term'_case(exp1, exp2)
      | (S.Lambda (x1, e1, t1), S.Lambda (x2, e2, t2)) =>
        let
          val x = S.Var (Symbol.fresh (Symbol.name x1, Symbol.get_type x1), Symbol.get_type x1)

          fun typescheme_toString t =
            let
              val (tyvarlist, typ) = t
            in
              case (!typ) of
                StaticObjectsCore.Determined (x) =>
                  "Determined\n" ^ (typescheme_toString (nil, x))
              | StaticObjectsCore.ConsType (x) =>
                  let
                    val (typlist, tyname) = x
                    val tyname_str = TyName.toString tyname
                  in
                    "Cons type, tyname is: " ^ tyname_str ^ "\n" 
                  end
              | StaticObjectsCore.TyVar (x) =>
                  "TyVar, which is: " ^ (TyVar.toString x) ^ "\n"
              | _ => "Something else\n"      
            end

          fun same_types_helper (t1, t2) =
            let
              val (tyvarlist1, typ1) = t1
              val (tyvarlist2, typ2) = t2

              fun same_typelist ([], []) = true
                | same_typelist ([], _) = false
                | same_typelist (_, []) = false
                | same_typelist (x::xs, y::ys) =
                    same_types_helper ((tyvarlist1, x),
                                       (tyvarlist2, y)) andalso
                    same_typelist (xs, ys)
            in
              case (!typ1, !typ2) of
                (StaticObjectsCore.Determined(typ1'), _) =>
                  same_types_helper ((tyvarlist1, typ1'), t2)
              | (_, StaticObjectsCore.Determined(typ2')) =>
                  same_types_helper (t1, (tyvarlist2, typ2'))
              | (StaticObjectsCore.TyVar(tyvar1),
                 StaticObjectsCore.TyVar(tyvar2)) =>
                  let
                    fun get_place_in_tyvarlist c ([], tyvar) = NONE
                      | get_place_in_tyvarlist c (x::xs, tyvar) =
                          if (TyVar.toString x = TyVar.toString tyvar) then SOME (c+1)
                          else get_place_in_tyvarlist (c+1) (xs, tyvar)
                  in
                    get_place_in_tyvarlist 0 (tyvarlist1, tyvar1) =
                    get_place_in_tyvarlist 0 (tyvarlist2, tyvar2)
                  end
              | (StaticObjectsCore.RowType(typelabmap1, rowvaropt1),
                 StaticObjectsCore.RowType(typelabmap2, rowvaropt2)) =>
                  let
                    val typelist1 = LabMap.listItems typelabmap1
                    val typelist2 = LabMap.listItems typelabmap2
                  in
                    same_typelist (typelist1, typelist2)
                  end
              | (StaticObjectsCore.FunType(hypothesis1, conclusion1),
                 StaticObjectsCore.FunType(hypothesis2, conclusion2)) =>
                  same_types_helper((tyvarlist1, hypothesis1), 
                                    (tyvarlist2, hypothesis2)) andalso
                  same_types_helper((tyvarlist1, conclusion1),
                                    (tyvarlist2, conclusion2))
              | (StaticObjectsCore.ConsType(typelist1, tyname1),
                 StaticObjectsCore.ConsType(typelist2, tyname2)) =>
                  if (
                  (TyName.toString tyname1) = (TyName.toString tyname2)
                  andalso same_typelist (typelist1, typelist2)
                  andalso 
                    List.exists (fn t => t = (TyName.toString tyname1))
                      shared_datatypes 
                      ) then true
                  else false
              | _ => false
            end
            
          fun same_types (type1, type2) =
            case (type1, type2) of
                 (Symbol.Unknown, Symbol.Unknown) => true
               | (Symbol.Known(_), Symbol.Unknown) => false
               | (Symbol.Unknown, Symbol.Known(_)) => false
               | (Symbol.Known(t1), Symbol.Known(t2)) =>
                   same_types_helper(t1, t2)
               | _ => raise Fail "Issue with hardcoded unit type"
        in
          if (same_types (Symbol.get_type x1, Symbol.get_type x2)) then
            generate_term (subst (x1, x) e1, subst (x2, x) e2)
          else False
        end
      | (S.App (S.Var (s1, var_t1), arg1, app_t1), S.App (S.Var (s2, var_t2), arg2, app_t2)) =>
        let
          val x1 = S.Var (Symbol.fresh_nameless app_t1, app_t1)
          val x2 = S.Var (Symbol.fresh_nameless app_t2, app_t2)
        in
          (
          Or [
            And [
              generate_term (S.Var (s1, var_t1), S.Var (s2, var_t2)),
              generate_term (arg1, arg2)
            ],
            generate_term (x1, subst_app_var(x1, s1, arg1) 
              (S.App (S.Var (s2, var_t2), arg2, app_t2))),
            generate_term (subst_app_var(x2, s2, arg2) 
              (S.App (S.Var (s1, var_t1), arg1, app_t1)), x2)
          ]
          )
        end
      | (S.App (S.Fix (s1, e1, fix_t1), arg1, app_t1), S.App (S.Var (s2, var_t2), arg2, app_t2)) =>
          let
            val x1 = S.Var (Symbol.fresh_nameless app_t1, app_t1)
            val x2 = S.Var (Symbol.fresh_nameless app_t2, app_t2)
          in
            Or [
              generate_term(x1, subst_app_fix(x1, s1, e1, arg1) 
                (S.App (S.Var (s2, var_t2), arg2, app_t2))),
              generate_term(subst_app_var(x2, s2, arg2) 
                (S.App (S.Fix (s1, e1, fix_t1), arg1, app_t1)), x2)
            ]
          end
      | (S.App (S.Var (s1, var_t1), arg1, app_t1), S.App (S.Fix (s2, e2, fix_t2), arg2, app_t2)) =>
          let
            val x1 = S.Var (Symbol.fresh_nameless app_t1, app_t1)
            val x2 = S.Var (Symbol.fresh_nameless app_t2, app_t2)
          in
            Or [
              generate_term(x1, subst_app_var(x1, s1, arg1) 
                (S.App (S.Fix (s2, e2, fix_t2), arg2, app_t2))),
              generate_term(subst_app_fix(x2, s2, e2, arg2) 
                (S.App (S.Var (s1, var_t1), arg1, app_t1)), x2)
            ]
          end
      | (S.App (S.Fix (s1, e1, fix_t1), arg1, app_t1), S.App (S.Fix (s2, e2, fix_t2), arg2, app_t2)) =>
          let
            val x1 = S.Var (Symbol.fresh_nameless app_t1, app_t1)
            val x2 = S.Var (Symbol.fresh_nameless app_t2, app_t2)
          in
            Or [
              And [
                generate_term (S.Fix (s1, e1, fix_t1), 
                               S.Fix (s2, e2, fix_t2)),
                generate_term (arg1, arg2)
              ],
              generate_term (x1, subst_app_fix(x1, s1, e1, arg1) 
                (S.App (S.Fix (s2, e2, fix_t2), arg2, app_t2))),
              generate_term (subst_app_fix(x2, s2, e2, arg2) 
                (S.App (S.Fix (s1, e1, fix_t1), arg1, app_t1)), x2)
            ]
          end
      | (S.App (f1, arg1, t1), S.App (f2, arg2, t2)) =>
          And [
            generate_term (f1, f2),
            generate_term (arg1, arg2)
          ]
      | (S.Fix (x1, e1, t1), S.Fix (x2, e2, t2)) =>
        let
          val x = S.Var (Symbol.fresh_nameless t1, t1)
        in
          generate_term (subst (x1, x) e1, subst (x2, x) e2)
        end
      | (S.Raise (e1, t1), S.Raise (e2, t2)) => generate_term (e1, e2)
      | (S.Proj (e1, s1, t1), S.Proj (e2, s2, t2)) =>
          (* This is more coarse than I would like, as it requires the whole
          * tuple of e1 and e2 to be the same, but since these expressions
          * already are in whnf, I can't decompose e1 or e2 into records, so
          * this is the best that can be done *)
          if (s1 = s2) then generate_term (e1, e2)
          else False
      | _ =>  if (exp1 = exp2) then True
              else False
    end

    (* An extension of generate_term' for when at least one of exp1 and exp2 is
       a case expression at the top node *)
    and generate_term'_case (exp1, exp2) =
      case (exp1, exp2) of
    ( (exp1 as S.Case (e1, match1, is_exhaustive1, t1), exp2)
    | (exp2, exp1 as S.Case (e1, match1, is_exhaustive1, t1)) ) => ( 
          if(is_exhaustive1 = S.NONEXHAUSTIVE) then False
          else
          case is_atomic e1 of
            SOME e1_term => 
              let
                fun add_index L =
                  let
                    fun add_index_helper (nil,  _) = nil
                      | add_index_helper (h::tl,i) = (h,i) :: add_index_helper (tl,1+i)
                  in
                     add_index_helper (L,0)
                  end

                val match1withindices = add_index match1
              in
                And (map (fn ((p1i, e1i), index) =>
                  let
                    val (p1i', e1i') = freshen (p1i, e1i)
                    val (p1i_eqs, p1i_term) = pat_to_term p1i'

                    val prevmatch1withindices = List.filter (fn (_, i) => i < index) match1withindices
                    val nopreviousmatchesterm = 
                      case prevmatch1withindices of
                           nil => True
                         | _ =>
                              And (map (fn ((prev_p1i, prev_e1i), previndex) =>
                                let
                                  val (prev_p1i', _) = freshen (prev_p1i, prev_e1i)
                                  val (prev_p1i_eqs, prev_p1i_term) = pat_to_term prev_p1i'
                                in
                                  Not (And (Equals [e1_term, prev_p1i_term] :: prev_p1i_eqs))
                                end 
                              ) prevmatch1withindices)
                  in
                    Implies [
                      And (nopreviousmatchesterm :: (Equals [e1_term, p1i_term] :: p1i_eqs)),
                      generate_term (e1i', exp2)
                    ]
                  end
                ) match1withindices)
              end  
          | NONE =>
          case match1 of
            [(S.VarPat (x, t), e1')] => generate_term (subst (x, e1) e1', exp2)
          | _ =>
          case exp2 of
            S.Case (e2, match2, is_exhaustive2, t2) => (
              if(is_exhaustive2 = S.NONEXHAUSTIVE) then False
              else
              case is_atomic e2 of
                SOME e2_term =>
                  let
                    fun add_index L =
                      let
                        fun add_index_helper (nil,  _) = nil
                          | add_index_helper (h::tl,i) = (h,i) :: add_index_helper (tl,1+i)
                      in
                         add_index_helper (L,0)
                      end

                    val match2withindices = add_index match2
                  in
                    And (map (fn ((p2i, e2i), index) =>
                      let
                        val (p2i', e2i') = freshen (p2i, e2i)
                        val (p2i_eqs, p2i_term) = pat_to_term p2i'

                        val prevmatch2withindices = List.filter (fn (_, i) => i < index) match2withindices
                        val nopreviousmatchesterm =
                          case prevmatch2withindices of
                               nil => True
                             | _ =>
                                  And (map (fn ((prev_p2i, prev_e2i), previndex) =>
                                    let
                                      val (prev_p2i', _) = freshen (prev_p2i, prev_e2i)
                                      val (prev_p2i_eqs, prev_p2i_term) = pat_to_term prev_p2i'
                                    in
                                      Not (And (Equals [e2_term, prev_p2i_term] :: prev_p2i_eqs))
                                    end
                                  ) prevmatch2withindices)
                      in
                        Implies [
                          And (nopreviousmatchesterm :: (Equals [e2_term, p2i_term] :: p2i_eqs)),
                          generate_term (exp1, e2i')
                        ]
                      end
                    ) match2withindices)
                  end
              | NONE =>
              case match2 of
                [(S.VarPat (x, t), e2')] => generate_term (exp1, subst (x, e2) e2')
              | _ => (* symmetric case *)
                let
                  val e1_type = get_typescheme_from_exp e1 
                  val x = S.Var (Symbol.fresh_nameless e1_type, e1_type)
                in
                  And [
                    generate_term (e1, e2),
                    generate_term (S.Case (x, match1, is_exhaustive1, t1), 
                                   S.Case (x, match2, is_exhaustive2, t2))
                  ]
                end
            )
          | _ => if (exp1 = exp2) then True
                 else False
        )
    | _ => raise Fail "Unreachable" 
      (* This breaks the requirement that generate_term'_case is only called when
         at least one of the expressions is a case expression at the top node *)

    val exps = (program1, program2)

    (*
      Since we're interested in whether equivalence is valid (not just satisfiable),
      we check the satisfiability of its negation.
      If the negation is satisfiable then the programs are not equivalent;
      if the negation is unsatisfiable then the programs are equivalent.
    *)
    val term = generate_term exps
    val smtlib_program =
      preamble @ [
        DefineFun ("equivalence-is-refutable", [], "Bool",
          And [prog_var_int_definition, prog_var_str_definition, (Not term)]
        ),
        Assert (Ident "equivalence-is-refutable"),
        CheckSat
      ]
  in
    case Solver.solve smtlib_program of
      Sat => false
    | Unsat => true
  end

end
