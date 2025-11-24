!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing remove-patternc ===" )
!(println! "")

!(println! "Test 1: Remove single atom with literal pattern")
!(add-atom &self (kb1 (Constant "0" (Type "$c"))))
!(test (collapse (match &self (kb1 (Constant "0" (Type "$c"))) found)) (found))
!(remove-patternc &self (kb1 (Constant "0" (Type "$c"))))
!(test (match &self (kb1 (Constant "0" (Type "$c"))) found) ())

!(println! "Test 2: Remove with variable in pattern")
!(add-atom &self (kb2 (Constant "+" (Type "$c"))))
!(test (collapse (match &self (kb2 (Constant $name (Type "$c"))) $name)) ("+"))
!(remove-patternc &self (kb2 (Constant $tok (Type "$c"))))
!(test (match &self (kb2 (Constant $name (Type "$c"))) $name) ())

!(println! "Test 3: Remove multiple matching atoms")
!(add-atom &self (kb3 (Var x (FSDepth 1) (Type "$v"))))
!(add-atom &self (kb3 (Var y (FSDepth 1) (Type "$v"))))
!(add-atom &self (kb3 (Var z (FSDepth 1) (Type "$v"))))
!(test (matchc &self (kb3 (Var $v (FSDepth 1) (Type "$v"))) $v) (x y z))
!(remove-patternc &self (kb3 (Var $v (FSDepth 1) (Type "$v"))))
!(test (matchc &self (kb3 (Var $v (FSDepth 1) (Type "$v"))) $v) ())

!(println! "Test 4: Remove only matching FSDepth level")
!(add-atom &self (kb4 (Var a (FSDepth 0) (Type "$v"))))
!(add-atom &self (kb4 (Var b (FSDepth 1) (Type "$v"))))
!(add-atom &self (kb4 (Var c (FSDepth 2) (Type "$v"))))
; Remove only level 1
!(remove-patternc &self (kb4 (Var $v (FSDepth 1) (Type "$v"))))
; Level 0 and 2 should remain
!(test (collapse (match &self (kb4 (Var a (FSDepth 0) (Type "$v"))) found)) (found))
!(test (match &self (kb4 (Var b (FSDepth 1) (Type "$v"))) found) ())
!(test (collapse (match &self (kb4 (Var c (FSDepth 2) (Type "$v"))) found)) (found))

!(println! "Test 5: Remove EList at specific level")
!(add-atom &self (kb5 (EList (FSDepth 0) (Cons (Cons symb|- (Cons symbP Nil)) Nil))))
!(add-atom &self (kb5 (EList (FSDepth 1) (Cons (Cons symb|- (Cons symbQ Nil)) Nil))))
!(test (matchc &self (kb5 (EList (FSDepth $l) $e)) $l) (0 1))
!(remove-patternc &self (kb5 (EList (FSDepth 0) $elist)))
!(test (matchc &self (kb5 (EList (FSDepth $l) $e)) $l) (1))

!(println! "Test 6: Remove FList at specific level")
!(add-atom &self (kb6 (FList (FSDepth 1) (Cons (Cons symbwff (Cons symbP Nil)) Nil))))
!(add-atom &self (kb6 (FList (FSDepth 2) (Cons (Cons symbterm (Cons symbt Nil)) Nil))))
!(test (matchc &self (kb6 (FList (FSDepth $l) $f)) $l) (1 2))
!(remove-patternc &self (kb6 (FList (FSDepth 2) $flist)))
!(test (matchc &self (kb6 (FList (FSDepth $l) $f)) $l) (1))

!(println! "Test 7: Remove DVar pairs")
!(add-atom &self (kb7 (DVar (x y) (FSDepth 0) (Type "$d"))))
!(add-atom &self (kb7 (DVar (x z) (FSDepth 0) (Type "$d"))))
!(test (matchc &self (kb7 (DVar $p (FSDepth 0) (Type "$d"))) $p) ((x y) (x z)))
!(remove-patternc &self (kb7 (DVar (x y) (FSDepth 0) (Type "$d"))))
!(test (matchc &self (kb7 (DVar $p (FSDepth 0) (Type "$d"))) $p) ((x z)))

!(println! "Test 8: Remove when pattern matches nothing")
!(add-atom &self (kb8 (Constant "0" (Type "$c"))))
; Try to remove something that doesn't exist
!(remove-patternc &self (kb8 (Var $v (FSDepth 0) (Type "$v"))))
; Constant should still be there
!(test (collapse (match &self (kb8 (Constant "0" (Type "$c"))) found)) (found))

!(println! "Test 9: Remove complex pattern (hypothesis)")
!(add-atom &self (kb9 ((Label ax1) FHyp (FSDepth 1) ((Typecode wff) (FVar ph) (Type "$f")))))
!(add-atom &self (kb9 ((Label ax2) EHyp (FSDepth 1) ((Statement (Cons symb|- (Cons symbP Nil))) (Type "$e")))))
!(test (matchc &self (kb9 ((Label $l) FHyp (FSDepth 1) $d)) $l) (ax1))
!(remove-patternc &self (kb9 ((Label $l) FHyp (FSDepth 1) $d)))
!(test (match &self (kb9 ((Label $l) FHyp (FSDepth 1) $d)) $l) ())
; EHyp should still be there
!(test (matchc &self (kb9 ((Label $l) EHyp (FSDepth 1) $d)) $l) (ax2))

!(println! "")
!(println! "=== All remove-patternc tests complete ✅ ===")
