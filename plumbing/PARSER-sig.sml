signature PARSER = 
sig
  val parse_code : string -> SyntaxProgram.Program
  val parse_files : string list -> SyntaxProgram.Program
end
