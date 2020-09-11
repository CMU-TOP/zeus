fun foo x =
  case x of
    NONE => 2
  | SOME y => (
      case y of
        SOME z => z
      | NONE => 1
    )