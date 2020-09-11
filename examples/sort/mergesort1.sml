type 'a ord = 'a * 'a -> order

fun split [] = ([], [])
  | split [x] = ([x] , [])
  | split (x::y::L) =
      let
        val (A, B) = split L
      in
        (x::A, y::B)
      end

fun merge (cmp : 'a ord, ([], L)) = L
  | merge (cmp : 'a ord, (L , [])) = L
  | merge (cmp : 'a ord, (x::xs, y::ys)) =
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
