fun foo x y z =
  if(x >= 0) then x + y > z
  else if(y >= 0) then x + y > z
  else if(z < 0) then x + y > z
  else false
