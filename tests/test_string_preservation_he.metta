!(bind! &kb (new-space))

!(println! "HE MeTTa: Testing string preservation in add-atom")
!(println! "")

!(println! "Adding with string: (Constant \"setvar\" (Type \"$c\"))")
!(add-atom &kb (Constant "setvar" (Type "$c")))

!(println! "Matching with string pattern:")
!(println! (match &kb (Constant "setvar" (Type "$c")) found-with-string))

!(println! "Matching with atom pattern:")
!(println! (match &kb (Constant setvar (Type "$c")) found-with-atom))

!(println! "What's actually stored:")
!(match &kb (Constant $x (Type $y)) (println! (Constant $x (Type $y))))
