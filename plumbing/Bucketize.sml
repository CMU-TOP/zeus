structure Bucketize : BUCKETIZE = 
struct
  fun bucketize eq =
  let
    fun add ((key, data), []) = [(data, [key])]
      | add ((key, data), (rep, mems)::buckets) = (
          (if Settings.verbose
            then print ("comparing " ^ key ^ " with bucket representative " ^ List.last mems ^ ": ")
            else ());
          if eq (data, rep)
          then (print (if Settings.verbose then "equivalent\n" else "0"); (rep, key::mems) :: buckets)
          else (print (if Settings.verbose then "not equivalent\n" else "X"); (rep, mems) :: add ((key, data), buckets))
        ) handle exn => (
          print ("Error when comparing " ^ key ^ " with bucket representative " ^ List.last mems ^ ":\n");
          List.app (fn s => print ("  " ^ s ^ "\n")) (SMLofNJ.exnHistory exn);
          (rep, mems) :: buckets
        )
  in
    map #2 o foldl add []
  end
end
