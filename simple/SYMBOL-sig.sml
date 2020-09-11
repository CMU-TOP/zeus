signature SYMBOL = 
sig
  datatype typescheme = Known of StaticObjectsCore.TypeScheme | Hardcoded of string | Unknown
  eqtype t
  val compare : t * t -> order
  val fresh : string * typescheme -> t
  val fresh_nameless : typescheme -> t
  val fresh' : unit -> t
  val global : string * typescheme -> t
  val is_global : t -> bool
  val guid : t -> int
  val name : t -> string
  val get_type : t -> typescheme
  val toString : t -> string
end
