fun foo x =
  case x of
    SOME (SOME y) => y
  | SOME NONE => 1
  | NONE => 2