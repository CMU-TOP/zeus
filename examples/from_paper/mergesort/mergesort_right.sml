fun split [] = ([] , [])
  | split (x::xs) =
      case xs of
        [] => ([x] , [])
      | (y::ys) =>
          let
            val (A , B) = split ys
          in
            (x::A, y::B)
          end

fun merge (l1 , l2) =
  case l1 of
    [] => l2
  | (x::xs) =>
      case l2 of
        [] => l1
      | (y::ys) =>
          if(x < y) then x::merge(xs, l2)
          else y::merge(l1, ys)

fun msort [] = []
  | msort [x] = [x]
  | msort L =
      let
        val (A , B) = split L
      in
        merge(msort A, msort B)
      end
