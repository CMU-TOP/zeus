signature SML_TO_SIMPLIFIED = 
sig
  structure M : ORD_MAP 

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

  val extract_from_decs : SyntaxCore.Dec list -> string -> 
                          (SimplifiedSyntax.exp * datatype_def M.map)
end
