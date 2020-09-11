structure Extract = 
struct
  structure A = Annotation
  structure SP = SyntaxProgram
  structure SM = SyntaxModule
  structure SC = SyntaxCore

  datatype module_identifier =
    Structure of string | Functor of string

  fun split_qualifiers [] = raise Fail "empty identifier"
    | split_qualifiers [id] = ([], id)
    | split_qualifiers (id::ids) =
      let val (structures, base_id) = split_qualifiers ids
      in (id::structures, base_id) end

  fun parse_identifier id =
    case String.tokens (fn c => c = #".") id of
      [] => raise Fail "empty identifier"
    | x::xs =>
      if String.isSuffix "()" x
      then (SOME (substring (x, 0, size x - 2)), split_qualifiers xs)
      else (NONE, split_qualifiers (x::xs))

  fun strDec_from_strExp strExp =
    case A.syntax strExp of
      SM.STRUCTStrExp strDec => SOME strDec
    | (SM.COLONStrExp (strExp', _) | SM.SEALStrExp (strExp', _) | SM.LETStrExp (_, strExp')) =>
      strDec_from_strExp strExp'
    | (SM.IDStrExp _ | SM.APPStrExp _) => NONE

  fun extract_structure_from_strBind strBind id s k =
    case A.syntax strBind of
      SM.StrBind (strId, strExp, strBind_opt) =>
      let fun k' () =
        if StrId.toString (A.syntax strId) = id
        then s (strDec_from_strExp strExp)
        else k ()
      in
        case strBind_opt of
          SOME strBind' => extract_structure_from_strBind strBind' id s k'
        | NONE => k' ()
      end

  fun extract_structure_from_strDec strDec id s k =
    case A.syntax strDec of
      SM.STRUCTUREStrDec strBind => extract_structure_from_strBind strBind id s k
    | SM.LOCALStrDec (_, strDec') => extract_structure_from_strDec strDec' id s k
    | SM.SEQStrDec (strDec1, strDec2) =>
      extract_structure_from_strDec strDec2 id s
        (fn () => extract_structure_from_strDec strDec1 id s k)
    | (SM.DECStrDec _ | SM.EMPTYStrDec) => k ()

  fun extract_structure_from_topDec topDec id s k =
    case A.syntax topDec of
      SM.STRDECTopDec (strDec, topDec_opt) =>
        let fun k' () = extract_structure_from_strDec strDec id s k
        in
          case topDec_opt of
            SOME topDec' => extract_structure_from_topDec topDec' id s k'
          | NONE => k' ()
        end
    | (SM.SIGDECTopDec (_, SOME topDec') | SM.FUNDECTopDec (_, SOME topDec')) =>
        extract_structure_from_topDec topDec' id s k
    | (SM.SIGDECTopDec (_, NONE) | SM.FUNDECTopDec (_, NONE)) => k ()

  fun extract_functor_from_funBind funBind id s k =
    case A.syntax funBind of
      SM.FunBind (funId, strId, sigExp, strExp, funBind_opt) =>
      let fun k' () =
        if FunId.toString (A.syntax funId) = id
        then s (strDec_from_strExp strExp)
        else k ()
      in
        case funBind_opt of
          SOME funBind' => extract_functor_from_funBind funBind' id s k'
        | NONE => k' ()
      end

  fun extract_functor_from_funDec funDec id s k =
    case A.syntax funDec of
      SM.FunDec funBind => extract_functor_from_funBind funBind id s k

  fun extract_functor_from_topDec topDec id s k =
    case A.syntax topDec of
      SM.FUNDECTopDec (funDec, topDec_opt) =>
        let fun k' () = extract_functor_from_funDec funDec id s k
        in
          case topDec_opt of
            SOME topDec' => extract_functor_from_topDec topDec' id s k'
          | NONE => k' ()
        end
    | (SM.SIGDECTopDec (_, SOME topDec') | SM.STRDECTopDec (_, SOME topDec')) =>
        extract_functor_from_topDec topDec' id s k
    | (SM.SIGDECTopDec (_, NONE) | SM.STRDECTopDec (_, NONE)) => k ()

  fun extract_module_from_topDec topDec (Structure id) =
        extract_structure_from_topDec topDec id
    | extract_module_from_topDec topDec (Functor id) =
        extract_functor_from_topDec topDec id

  fun extract_module_from_program program id s k =
    case A.syntax program of
      SP.Program (topDec, program_opt) =>
        let fun k' () = extract_module_from_topDec topDec id s k
        in
          case program_opt of
            SOME program' => extract_module_from_program program' id s k'
          | NONE => k' ()
        end

  fun declarations_in_strDec strDec =
    case A.syntax strDec of
      SM.DECStrDec dec => [dec]
    | SM.LOCALStrDec (_, strDec') => declarations_in_strDec strDec'
    | SM.SEQStrDec (strDec1, strDec2) =>
        declarations_in_strDec strDec1 @ declarations_in_strDec strDec2
    | (SM.STRUCTUREStrDec _ | SM.EMPTYStrDec) => []
  fun declarations_in_topDec topDec =
    case A.syntax topDec of
      SM.STRDECTopDec (strDec, topDec_opt) =>
        declarations_in_strDec strDec @
        getOpt (Option.map declarations_in_topDec topDec_opt, [])
    | (SM.SIGDECTopDec (_, topDec_opt) | SM.FUNDECTopDec (_, topDec_opt)) =>
        getOpt (Option.map declarations_in_topDec topDec_opt, [])
  fun declarations_in_program program = 
    case A.syntax program of
      SP.Program (topDec, program_opt) =>
        declarations_in_topDec topDec @
        getOpt (Option.map declarations_in_program program_opt, [])

  fun extract_from_strDec strDec ([], id) =
      SmlToSimplified.extract_from_decs (declarations_in_strDec strDec) id
    | extract_from_strDec strDec (s::ss, id) =
      extract_structure_from_strDec strDec s
      (fn NONE => raise Fail ("structure " ^ s ^ " bound to non-literal")
        | SOME strDec => extract_from_strDec strDec (ss, id))
      (fn () => raise Fail ("unable to find structure " ^ s))
  fun extract_from_program program (NONE, ([], id)) =
      SmlToSimplified.extract_from_decs (declarations_in_program program) id
    | extract_from_program program (NONE, (s::ss, id)) =
      extract_module_from_program program (Structure s)
      (fn NONE => raise Fail ("structure " ^ s ^ " bound to non-literal")
        | SOME strDec => extract_from_strDec strDec (ss, id))
      (fn () => raise Fail ("unable to find structure " ^ s))
    | extract_from_program program (SOME id, ids) =
      extract_module_from_program program (Functor id)
      (fn NONE => raise Fail ("functor " ^ id ^  " bound to non-literal")
        | SOME strDec => extract_from_strDec strDec ids)
      (fn () => raise Fail ("unable to find functor " ^ id))

  fun extract_code code identifier =
    extract_from_program (Parser.parse_code (code ^ ";")) (parse_identifier identifier)

  fun extract_files files identifier =
    extract_from_program (Parser.parse_files files) (parse_identifier identifier)

end
