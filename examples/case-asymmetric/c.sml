fun foo x =
  case x of
    SOME NONE => 1
  | SOME (SOME y) => y
  | NONE => 2