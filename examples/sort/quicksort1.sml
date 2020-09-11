type 'a ord = 'a * 'a -> order

fun pivotSplit (cmp: 'a ord, p: 'a, []: 'a list): 'a list * 'a list = ([],[])
  | pivotSplit (cmp, p, x::xs) =
    let
      val (A: 'a list, B: 'a list) = pivotSplit(cmp, p, xs)
    in
      (case cmp(x, p) of
          LESS => (x::A, B)
        | _ => (A, x::B))
    end

fun sort (cmp: 'a ord, []: 'a list): 'a list = []
  | sort (cmp, x::L) = 
    let
      val (A: 'a list, B: 'a list) = pivotSplit(cmp, x, L)
    in
      sort(cmp, A) @ (x::sort(cmp, B))
    end

