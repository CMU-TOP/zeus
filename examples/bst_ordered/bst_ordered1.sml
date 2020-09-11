datatype Tree = Leaf | Node of Tree * int * Tree

(* The only difference between this function and the function written in
  * bst_ordered2.sml is between leq and geq. In the general case, where leq and
  * geq can be arbitrary 'a * 'a -> order functions, the bst_ordered written in
  * this file is genuinely not equivalent from the function written in
  * bst_ordered2.sml (this can be seen by considering the behavior when
  * bst_ordered is given a nonsensical comparison function). But when a concrete
  * comparison function is given, as in the case of int_bst_ordered, Z3 is able
  * to use its understanding of the relationship between <= and >= to recognize
  * equivalence. So although bst_ordered is not equivalent between this file and
  * bst_ordered2.sml, int_bst_ordered is equivalent between the two files. *) 

fun bst_ordered leq T =
  let
    fun bst_ordered_helper Leaf = (true, NONE, NONE)
      | bst_ordered_helper (Node (L, x, R)) =
          let
            val (L_ordered, L_min_opt, L_max_opt) = bst_ordered_helper L
            val (R_ordered, R_min_opt, R_max_opt) = bst_ordered_helper R

            val left_tree_smaller =
             case L_max_opt of
                  NONE => true
                | SOME(L_max) => leq(L_max, x)
                    
            val right_tree_bigger =
              case R_min_opt of
                   NONE => true
                 | SOME(R_min) => leq(x, R_min)
                     
            val is_ordered =
              L_ordered andalso R_ordered andalso
              left_tree_smaller andalso right_tree_bigger

            val min =
              case L_min_opt of
                   NONE => x
                 | SOME(L_min) => L_min

            val max =
              case L_max_opt of
                   NONE => x
                 | SOME(L_max) => L_max
          in
            (is_ordered, SOME(min), SOME(max)) 
          end
  in
    #1 (bst_ordered_helper T)
  end

val int_bst_ordered = bst_ordered (op <=)
