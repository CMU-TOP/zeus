type 'a ord = 'a * 'a -> order

fun pivotSplit (cmp: 'a ord, p, []): 'a list * 'a list = ([],[])
  | pivotSplit (cmp, p, x::xs) =
    (case (cmp(x, p)) of
        LESS => (x::(#1 (pivotSplit(cmp, p, xs))), #2 (pivotSplit(cmp, p, xs)))
      | EQUAL => ((#1 (pivotSplit(cmp, p, xs))), x::(#2 (pivotSplit(cmp, p, xs))))
      | GREATER => ((#1 (pivotSplit(cmp, p, xs))), x::(#2 (pivotSplit(cmp, p, xs)))))

fun sort (cmp: 'a ord, []) = []
  | sort (cmp, x::L) = 
      sort(cmp, (#1 (pivotSplit(cmp, x, L)))) @
      x::sort(cmp, (#2 (pivotSplit(cmp, x, L))))
