!(import! &self ../../../PeTTa/lib/lib_he)

!(println! "=== Testing Prolog string comparison ===")

; Import Prolog's @< (atom comparison)
!(import_prolog_function @<)

!(println! "Test 1: Direct @< calls")
!(println! (@< x y))
!(println! (@< y x))
!(println! (@< a b))
!(println! (@< b a))
!(println! (@< ph ps))

; Define wrapper
(= (string< $x $y) (@< $x $y))

!(println! "Test 2: Via wrapper")
!(println! (string< x y))
!(println! (string< y x))
!(println! (string< a z))
!(println! (string< z a))

; Test orient_pair with proper string<
(= (orient_pair $x $y)
   (if (string< $x $y)
       ($x $y)
       ($y $x)))

!(println! "Test 3: orient_pair with proper ordering")
!(println! (orient_pair x y))
!(println! (orient_pair y x))
!(println! (orient_pair a z))
!(println! (orient_pair z a))
