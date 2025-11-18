; Unit tests for remove-patternc helper function
; remove-patternc removes all atoms matching a pattern from a space

; Test helper
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (test $actual $expected) (assertEqual $actual $expected))

; Helper functions
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (remove-patternc $space $pattern)
   (collapse (let $pattern (match $space $pattern $pattern) (remove-atom $space $pattern))))

!(println! "=== remove-patternc Tests ===")
!(println! "")

!(println! "Test 1: Remove single atom with literal pattern")
!(bind! &kb1 (new-space))
!(add-atom &kb1 (Constant "0" (Type "$c")))
!(test (match &kb1 (Constant "0" (Type "$c")) "found") "found")
!(remove-patternc &kb1 (Constant "0" (Type "$c")))
!(test (match &kb1 (Constant "0" (Type "$c")) "found") ())

!(println! "Test 2: Remove with variable in pattern")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Constant "+" (Type "$c")))
!(test (match &kb2 (Constant $name (Type "$c")) $name) "+")
!(remove-patternc &kb2 (Constant $tok (Type "$c")))
!(test (match &kb2 (Constant $name (Type "$c")) $name) ())

!(println! "Test 3: Remove multiple matching atoms")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Var "x" (FSDepth 1) (Type "$v")))
!(add-atom &kb3 (Var "y" (FSDepth 1) (Type "$v")))
!(add-atom &kb3 (Var "z" (FSDepth 1) (Type "$v")))
!(test (matchc &kb3 (Var $v (FSDepth 1) (Type "$v")) $v) ("x" "y" "z"))
!(remove-patternc &kb3 (Var $v (FSDepth 1) (Type "$v")))
!(test (matchc &kb3 (Var $v (FSDepth 1) (Type "$v")) $v) ())

!(println! "Test 4: Remove only matching FSDepth level")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var "a" (FSDepth 0) (Type "$v")))
!(add-atom &kb4 (Var "b" (FSDepth 1) (Type "$v")))
!(add-atom &kb4 (Var "c" (FSDepth 2) (Type "$v")))
; Remove only level 1
!(remove-patternc &kb4 (Var $v (FSDepth 1) (Type "$v")))
; Level 0 and 2 should remain
!(test (match &kb4 (Var "a" (FSDepth 0) (Type "$v")) "found") "found")
!(test (match &kb4 (Var "b" (FSDepth 1) (Type "$v")) "found") ())
!(test (match &kb4 (Var "c" (FSDepth 2) (Type "$v")) "found") "found")

!(println! "Test 5: Remove EList at specific level")
!(bind! &kb5 (new-space))
!(add-atom &kb5 (EList (FSDepth 0) (("|-" "P"))))
!(add-atom &kb5 (EList (FSDepth 1) (("|-" "Q"))))
!(test (matchc &kb5 (EList (FSDepth $l) $e) $l) (0 1))
!(remove-patternc &kb5 (EList (FSDepth 0) $elist))
!(test (matchc &kb5 (EList (FSDepth $l) $e) $l) (1))

!(println! "Test 6: Remove FList at specific level")
!(bind! &kb6 (new-space))
!(add-atom &kb6 (FList (FSDepth 1) (("wff" "P"))))
!(add-atom &kb6 (FList (FSDepth 2) (("term" "t"))))
!(test (matchc &kb6 (FList (FSDepth $l) $f) $l) (1 2))
!(remove-patternc &kb6 (FList (FSDepth 2) $flist))
!(test (matchc &kb6 (FList (FSDepth $l) $f) $l) (1))

!(println! "Test 7: Remove DVar pairs")
!(bind! &kb7 (new-space))
!(add-atom &kb7 (DVar (x y) (FSDepth 0) (Type "$d")))
!(add-atom &kb7 (DVar (x z) (FSDepth 0) (Type "$d")))
!(test (matchc &kb7 (DVar $p (FSDepth 0) (Type "$d")) $p) ((x y) (x z)))
!(remove-patternc &kb7 (DVar (x y) (FSDepth 0) (Type "$d")))
!(test (matchc &kb7 (DVar $p (FSDepth 0) (Type "$d")) $p) ((x z)))

!(println! "Test 8: Remove with variable bound from state")
!(bind! &kb8 (new-space))
!(bind! &fd8 (new-state 3))
!(change-state! &fd8 3)
!(add-atom &kb8 (Var "x" (FSDepth 3) (Type "$v")))
!(test (match &kb8 (Var "x" (FSDepth 3) (Type "$v")) "found") "found")
!(let $level (get-state &fd8)
  (remove-patternc &kb8 (Var $v (FSDepth $level) (Type "$v"))))
!(test (match &kb8 (Var "x" (FSDepth 3) (Type "$v")) "found") ())

!(println! "Test 9: Remove when pattern matches nothing")
!(bind! &kb9 (new-space))
!(add-atom &kb9 (Constant "0" (Type "$c")))
; Try to remove something that doesn't exist
!(remove-patternc &kb9 (Var $v (FSDepth 0) (Type "$v")))
; Constant should still be there
!(test (match &kb9 (Constant "0" (Type "$c")) "found") "found")

!(println! "Test 10: Remove complex pattern (hypothesis)")
!(bind! &kb10 (new-space))
!(add-atom &kb10 ((Label "ax1") FHyp (FSDepth 1) ((Typecode "wff") (FVar "ph") (Type "$f"))))
!(add-atom &kb10 ((Label "ax2") EHyp (FSDepth 1) ((Statement ("|-" "P")) (Type "$e"))))
!(test (matchc &kb10 ((Label $l) FHyp (FSDepth 1) $d) $l) ("ax1"))
!(remove-patternc &kb10 ((Label $l) FHyp (FSDepth 1) $d))
!(test (matchc &kb10 ((Label $l) FHyp (FSDepth 1) $d) $l) ())
; EHyp should still be there
!(test (matchc &kb10 ((Label $l) EHyp (FSDepth 1) $d) $l) ("ax2"))

!(println! "")
!(println! "=== All remove-patternc tests complete ===")
