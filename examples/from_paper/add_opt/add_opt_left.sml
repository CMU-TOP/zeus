fun add_opt x y =
  case (x, y) of
    (SOME m, SOME n) => SOME (m + n)
  | (NONE, _) => NONE
  | (_, NONE) => NONE
