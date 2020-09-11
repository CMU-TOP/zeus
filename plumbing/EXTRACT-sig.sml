signature EXTRACT = 
sig
  (* takes a string containing SML code then a string representing an SML
    identifier, and returns the expression bound at that identifier, if it can
    be found. Raises Fail if unable to find. Is able to look inside structures. *)
  val extract_code : string -> string -> 
                (SimplifiedSyntax.exp * SmlToSimplified.datatype_def_map)

  val extract_files : string list -> string -> 
                (SimplifiedSyntax.exp * SmlToSimplified.datatype_def_map)
end
