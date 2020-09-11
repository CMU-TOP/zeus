fun bind a f =
  case a of
    SOME b => f b
  | NONE => NONE

val return = SOME

fun add_opt x y =
  bind x (fn m =>
  bind y (fn n =>
    return ( m + n )
  ))
