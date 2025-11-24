!(println! "=== Testing string comparison options ===")

; Import Prolog term comparison
!(import_prolog_function @<)

; Test 1: Try @< directly on atoms
!(println! "Test 1: @< on atoms")
!(println! (@< a b))
!(println! (@< b a))
!(println! (@< x y))
!(println! (@< y x))

; Test 2: Try @< on strings
!(println! "Test 2: repr then compare")
!(let ($s1 $s2) ((repr a) (repr b))
  (println! ($s1 $s2 (@< $s1 $s2))))

; Test 3: Check what @< returns with numbers
!(println! "Test 3: @< with numbers")
!(println! (@< 1 2))
!(println! (@< 2 1))
