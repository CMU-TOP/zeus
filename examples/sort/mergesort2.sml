type 'a ord = 'a * 'a -> order

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

fun merge (cmp : 'a ord, (l1 , l2)) =
  case l1 of
    [] => l2
  | (x::xs) =>
      case l2 of
        [] => l1
      | (y::ys) =>
          (case (cmp(x, y)) of
            LESS => x::merge(cmp, (xs, y::ys))
          | _ => y::merge(cmp, (x::xs, ys)))

fun sort (cmp : 'a ord, []) = []
  | sort (cmp : 'a ord, [x]) = [x]
  | sort (cmp : 'a ord, L) =
      let
        val (A , B) = split L
      in
        merge(cmp, (sort(cmp, A), sort(cmp, B)))
      end
