; Debug make_assertion to see what's happening

(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

(= (add_mand_var $kb $tok)
  (unify $kb (Var $tok $_ (Type "$v"))
    (unify $kb (MandVar $tok) () (add-atom $kb (MandVar $tok))) ()))

!(bind! &kb (new-space))
!(add-atom &kb (Var t 1 (Type "$v")))
!(add-atom &kb (Var r 1 (Type "$v")))

!(println! "Variables defined:")
!(println! (matchc &kb (Var $v $_ (Type "$v")) $v))

!(println! "")
!(println! "Adding mandatory vars from statement (term (t + r)):")
!(map-atom (term (t + r)) $tok (add_mand_var &kb $tok))

!(println! "")
!(println! "Mandatory vars:")
!(println! (matchc &kb (MandVar $v) $v))
