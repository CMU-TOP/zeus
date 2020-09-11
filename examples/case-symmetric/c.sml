val s = 
  let
    fun toString true = "true"
      | toString false = "false"
  in
    toString (1 = 1)
  end
