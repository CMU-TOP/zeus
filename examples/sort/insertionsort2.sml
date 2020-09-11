type 'a ord = 'a * 'a -> order

fun insertElement (cmp : 'a ord, x, L) =
  case L of
    [] => [x]
  | (y::ys) =>
      (case cmp(x, y) of
            LESS => x::(y::ys)
          | _ => y::insertElement(cmp, x, ys))

fun sort (cmp : 'a ord, L) =
  case L of
      [] => []
    | (x::xs) => 
        let
          val sorted_tail = sort(cmp, xs)
        in
          insertElement(cmp, x, sorted_tail)
        end
