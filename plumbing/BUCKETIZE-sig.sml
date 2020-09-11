signature BUCKETIZE =
sig
  val bucketize : ('a * 'a -> bool) -> (string * 'a) list -> string list list
end