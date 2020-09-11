structure Solver : sig
  val solve : SMTLib.command list -> SMTLib.response
end = struct
  fun solve commands =
    let
      val commands_file_path = OS.FileSys.tmpName ()
      val response_file_path = OS.FileSys.tmpName ()
      val command_string = "z3 -smt2 " ^ commands_file_path ^ " > " ^ response_file_path
      val () = if(Settings.save_SMT_formula) then print (command_string ^ "\n") else ()
    in
      SMTLibUtils.write_commands_to_file commands_file_path commands;
      (if (OS.Process.isSuccess (OS.Process.system command_string))
      then () else print ("Something went wrong; got a bad exit status from z3\n"));
      SMTLibUtils.read_response_from_file response_file_path before 
        (if(Settings.save_SMT_formula) then () else
          (
            OS.FileSys.remove commands_file_path;
            OS.FileSys.remove response_file_path
          )
        )
    end
end
