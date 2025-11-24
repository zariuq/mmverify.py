!(println! "PeTTa: Testing string preservation in add-atom")
!(println! "")

!(println! "Adding with string: (Constant \"setvar\" (Type \"$c\"))")
!(add-atom &self (testkb (Constant "setvar" (Type "$c"))))

!(println! "Matching with string pattern:")
!(println! (collapse (match &self (testkb (Constant "setvar" (Type "$c"))) found-with-string)))

!(println! "Matching with atom pattern:")
!(println! (collapse (match &self (testkb (Constant setvar (Type "$c"))) found-with-atom)))

!(println! "What's actually stored (with types):")
!(match &self (testkb (Constant $x (Type $y)))
  (println! ("  Constant value:" $x "  type:" (get-type $x))))
