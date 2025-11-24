!(println! "Testing if match works with string constants")

!(add-atom &self (testkb (Constant "setvar" (Type "$c"))))

!(println! "Direct match with literal string:")
!(println! (collapse (match &self (testkb (Constant "setvar" (Type "$c"))) found)))

!(println! "Match with variable $typecode:")
!(println! (collapse (match &self (testkb (Constant $typecode (Type "$c"))) found)))

!(println! "What did $typecode bind to?")
!(match &self (testkb (Constant $typecode (Type "$c")))
  (println! ("  typecode:" $typecode "  type:" (get-type $typecode))))
