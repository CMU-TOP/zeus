fun split [] = ([], [])
  | split [x] = ([x] , [])
  | split (x::y::L) =
      let
        val (A, B) = split L
      in
        (x::A, y::B)
      end

fun merge ([], L) = L
  | merge (L , []) = L
  | merge (x::xs, y::ys) =
      if(x < y) then x::merge(xs, y::ys)
      else y::merge(x::xs, ys)

fun msort [] = []
  | msort [x] = [x]
  | msort L =
      let
        val (A , B) = split L
      in
        merge (msort A, msort B)
      end
