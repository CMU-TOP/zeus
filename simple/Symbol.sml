structure Symbol : SYMBOL = 
struct
  datatype typescheme = Known of StaticObjectsCore.TypeScheme | Hardcoded of string | Unknown

  (* invariant: if n1 = n2, then (n1, s1, t1) = (n2, s2, t2) *)
  type t = int * string * typescheme 

  val counter = ref 0

  fun compare ((n1, _, _), (n2, _, _)) = Int.compare (n1, n2)

  fun fresh (s, t) = (
    (counter := !counter + 1; !counter), s, t 
  )

  fun fresh_nameless t = fresh ("%a", t)

  fun fresh' () = fresh ("%a", Unknown)

  structure M = BinaryMapFn(
    type ord_key = string
    val compare = String.compare
  )

  val globals : (int * typescheme) M.map ref = ref M.empty

  fun global (s, t) =
    case M.find (!globals, s) of
      SOME (n, _) => (n, s, t)
    | NONE =>
      let val (n, _, _) = fresh (s, t) in
        globals := M.insert (!globals, s, (n, t));
        (n, s, t)
      end

  fun is_global (n, s, _) =
    case M.find (!globals, s) of
      NONE => false
    | SOME (m, _) => n = m

  fun guid (n, _, _) = n
  fun name (_, s, _) = s
  fun get_type (_, _, t) = t
  fun toString (n, s, Unknown) = s ^ Int.toString n
    | toString (n, s, Hardcoded(t)) = (s ^ (Int.toString n)) ^ " : " ^ t
    | toString (n, s, Known(t)) = (s ^ (Int.toString n)) 
  end
