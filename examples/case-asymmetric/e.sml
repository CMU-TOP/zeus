fun foo (SOME (SOME x)) = x
  | foo (SOME NONE) = 1
  | foo NONE = 2