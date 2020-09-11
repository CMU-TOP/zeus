structure Top = 
struct
  fun extract_file filename =
    let
      val file = TextIO.openIn filename
      val source = TextIO.inputAll file
      val _ = TextIO.closeIn file
    in
      Extract.extract_code source
    end

  fun extract_files filenames =
    Extract.extract_files filenames

  fun extract_from_dirstream dirname dirstream valname =
    case OS.FileSys.readDir dirstream of
      NONE => []
    | SOME filename => (
      let
        val exp = extract_file
          (OS.Path.joinDirFile {dir=dirname, file=filename})
          valname
      in
        (filename, exp) :: extract_from_dirstream dirname dirstream valname
      end
      handle
        IO.Io _ => (
          print "unable to open ";
          print filename;
          print "\n";
          extract_from_dirstream dirname dirstream valname
        )
      | Error.Error => (
          print "unable to parse ";
          print filename;
          print "\n";
          extract_from_dirstream dirname dirstream valname
        )
      | Fail msg => (
          print "unable to simplify ";
          print filename;
          print ": ";
          print msg;
          print "\n";
          extract_from_dirstream dirname dirstream valname
        )
      | Abort => (
          print "abort called on ";
          print filename;
          print "\n";
          extract_from_dirstream dirname dirstream valname
      ))

  fun extract_from_dirstream_with_lib dirname dirstream valname libname =
    case OS.FileSys.readDir dirstream of
      NONE => []
    | SOME filename => (
      let
        val exp = extract_files
          [libname, (OS.Path.joinDirFile {dir=dirname, file=filename})]
          valname
      in
        (filename, exp) :: extract_from_dirstream_with_lib dirname dirstream valname libname
      end
      handle
        IO.Io _ => (
          print "unable to open ";
          print filename;
          print "\n";
          extract_from_dirstream_with_lib dirname dirstream valname libname
        )
      | Error.Error => (
          print "unable to parse ";
          print filename;
          print "\n";
          extract_from_dirstream_with_lib dirname dirstream valname libname
        )
      | Fail msg => (
          print "unable to simplify ";
          print filename;
          print ": ";
          print msg;
          print "\n";
          extract_from_dirstream_with_lib dirname dirstream valname libname
        )
      | Abort => (
          print "abort called on ";
          print filename;
          print "\n";
          extract_from_dirstream_with_lib dirname dirstream valname libname 
      ))

  fun print_bucket mems = (
    print ("Bucket with " ^ Int.toString (length mems) ^ " members:\n");
    List.app (fn s=> (print "  "; print s; print "\n")) mems
  )
  
  fun print_buckets buckets = (
    print ("\n" ^ Int.toString (length buckets) ^ " buckets\n");
    List.app print_bucket buckets
  )

  fun bucketize_dir dirname valname =
    let
      val dirstream = OS.FileSys.openDir dirname
      val extracted = extract_from_dirstream dirname dirstream valname

      val timer = Timer.startRealTimer ()
      val buckets = Bucketize.bucketize Isomorphism.is_isomorphic extracted
      val () = print "Time (ms): "
      val () = print (Int.toString (Int.fromLarge (Time.toMilliseconds (Timer.checkRealTimer timer))))
      val () = print "\n"
      
      val sorted = ListMergeSort.sort
        (fn (L1, L2) => length L1 < length L2) buckets

      fun count_num_submissions [] = 0
        | count_num_submissions (bucket::rest) =
            (List.length bucket) + (count_num_submissions rest)

      val numSubmissions = count_num_submissions sorted
      val ninety_percentsubmissions =
        ((numSubmissions * 9) div 10) +
        (if((numSubmissions * 9) mod 10 = 0) then 0
         else 1)
      val seventy_five_percentsubmissions =
        ((numSubmissions * 3) div 4) +
        (if((numSubmissions * 3) mod 4 = 0) then 0
         else 1)

      fun find_percent_eq [] numLeftToFill = 0
        | find_percent_eq (bucket::rest) numLeftToFill =
            let
              val num_in_bucket = length bucket
              val numLeftToFill' = numLeftToFill - num_in_bucket
            in
              if(numLeftToFill' > 0) then 
                1 + (find_percent_eq rest numLeftToFill')
              else 1
            end

      fun find_num_nonsingleton_buckets [] = 0
        | find_num_nonsingleton_buckets ([mem]::rest) = 0
        | find_num_nonsingleton_buckets (mems::rest) =
            1 + (find_num_nonsingleton_buckets rest)

      val () = print "Total number of submissions: "
      val () = print (Int.toString numSubmissions)
      val () = print "\n"
      val () = print "Number of buckets that have 90% of submissions: "
      val () = print (Int.toString (find_percent_eq sorted ninety_percentsubmissions))
      val () = print "\n"
      val () = print "Number of buckets that have 75% of submissions: "
      val () = print (Int.toString (find_percent_eq sorted seventy_five_percentsubmissions))
      val () = print "\n"
      val () = print "Number of nonsingleton buckets: "
      val () = print (Int.toString (find_num_nonsingleton_buckets sorted))
      val () = print "\n"
    in
      print_buckets sorted
    end

  (* Note: The semantics of the functions and expressions defined in the shared
  * lib are not actually used. Using this function makes it so that if two
  * programs both refer to a shared library function, that shared library
  * function will be recognized as the same across both programs. But the actual
  * definition of said library function will not be used *)
  fun bucketize_dir_with_shared_lib libname dirname valname =
    let
      val dirstream = OS.FileSys.openDir dirname
      val extracted = extract_from_dirstream_with_lib dirname dirstream valname libname

      val timer = Timer.startRealTimer ()
      val buckets = Bucketize.bucketize Isomorphism.is_isomorphic extracted
      val () = print "Time (ms): "
      val () = print (Int.toString (Int.fromLarge (Time.toMilliseconds (Timer.checkRealTimer timer))))
      val () = print "\n"

      val sorted = ListMergeSort.sort
        (fn (L1, L2) => length L1 < length L2) buckets

      fun count_num_submissions [] = 0
        | count_num_submissions (bucket::rest) =
            (List.length bucket) + (count_num_submissions rest)

      val numSubmissions = count_num_submissions sorted
      val ninety_percentsubmissions =
        ((numSubmissions * 9) div 10) +
        (if((numSubmissions * 9) mod 10 = 0) then 0
         else 1)
      val seventy_five_percentsubmissions =
        ((numSubmissions * 3) div 4) +
        (if((numSubmissions * 3) mod 4 = 0) then 0
         else 1)

      fun find_percent_eq [] numLeftToFill = 0
        | find_percent_eq (bucket::rest) numLeftToFill =
            let
              val num_in_bucket = length bucket
              val numLeftToFill' = numLeftToFill - num_in_bucket
            in
              if(numLeftToFill' > 0) then 
                1 + (find_percent_eq rest numLeftToFill')
              else 1
            end

      fun find_num_nonsingleton_buckets [] = 0
        | find_num_nonsingleton_buckets ([mem]::rest) = 0
        | find_num_nonsingleton_buckets (mems::rest) =
            1 + (find_num_nonsingleton_buckets rest)

      val () = print "Total number of submissions: "
      val () = print (Int.toString numSubmissions)
      val () = print "\n"
      val () = print "Number of buckets that have 90% of submissions: "
      val () = print (Int.toString (find_percent_eq sorted ninety_percentsubmissions))
      val () = print "\n"
      val () = print "Number of buckets that have 75% of submissions: "
      val () = print (Int.toString (find_percent_eq sorted seventy_five_percentsubmissions))
      val () = print "\n"
      val () = print "Number of nonsingleton buckets: "
      val () = print (Int.toString (find_num_nonsingleton_buckets sorted))
      val () = print "\n"
    in
      print_buckets sorted
    end

  fun println s = print (s ^ "\n")
  fun simplify_file filename =
    println o SimplifiedUtils.toString o 
    (fn (simplified_program, _) => simplified_program) o
    extract_file filename

  fun simplify_files filenames =
    println o SimplifiedUtils.toString o 
    (fn (simplified_program, _) => simplified_program) o
    extract_files filenames

  fun isomorphic filename1 filename2 valname =
    println (Bool.toString (Isomorphism.is_isomorphic (
      extract_file filename1 valname,
      extract_file filename2 valname 
    )))

  (* Note: This allows a program to reference a function or expression defined
  * in another file, but it will not actually use the semantics of that function
  * or expression in said file. This is essentially a shortcut to avoid
  * typechecking errors, and shouldn't be used except in the special case of
  * when two programs both use a shared additional file (e.g. a file that acts
  * like a library *)
  fun isomorphic_multiple_files filenames1 filenames2 valname =
    println (Bool.toString (Isomorphism.is_isomorphic (
      extract_files filenames1 valname,
      extract_files filenames2 valname 
    )))
  end
