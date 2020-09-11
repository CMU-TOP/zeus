signature SMT_LIB_UTILS = 
sig
  val write_commands_to_file : string -> SMTLib.command list -> unit
  val read_response_from_file : string -> SMTLib.response
end
