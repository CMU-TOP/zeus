fun foo x =
  case x of
    SOME y => (
      case y of
        SOME z => z
      | NONE => 1
    )
  | NONE => 2