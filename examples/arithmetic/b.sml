fun not true = false
  | not false = true

fun foo x y z = not (x + y <= z)