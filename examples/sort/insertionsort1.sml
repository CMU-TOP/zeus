type 'a ord = 'a * 'a -> order

fun insertElement (cmp : 'a ord, x, []) = [x]
  | insertElement (cmp : 'a ord, x, y::ys) =
      (case cmp (x, y) of
           LESS => x::(y::ys)
         | _ => y::insertElement(cmp, x, ys))

fun sort (cmp : 'a ord, []) = []
  | sort (cmp : 'a ord, x::xs) = insertElement(cmp, x, sort(cmp, xs))
