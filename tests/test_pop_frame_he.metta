; Comprehensive tests for pop-frame
; Critical function for frame stack management

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== pop-frame Tests ===")
!(println! "")

!(println! "Test 1: pop-frame removes EList at current level")
!(bind! &kb1 (new-space))
!(bind! &fd1 (new-state 0))
!(push-frame &fd1)
; Add EList at level 1
!(add-atom &kb1 (EList (FSDepth 1) (("|-" "P"))))
!(test (matchc &kb1 (EList (FSDepth $l) $e) $l) (1))
; Pop should remove it
!(pop-frame &kb1 &fd1)
!(test (matchc &kb1 (EList (FSDepth $l) $e) $l) ())

!(println! "Test 2: pop-frame removes FList at current level")
!(bind! &kb2 (new-space))
!(bind! &fd2 (new-state 0))
!(push-frame &fd2)
; Add FList at level 1
!(add-atom &kb2 (FList (FSDepth 1) (("wff" "P"))))
!(test (matchc &kb2 (FList (FSDepth $l) $f) $l) (1))
; Pop should remove it
!(pop-frame &kb2 &fd2)
!(test (matchc &kb2 (FList (FSDepth $l) $f) $l) ())

!(println! "Test 3: pop-frame removes all entries at current level (using workflow functions)")
!(bind! &kb3 (new-space))
!(bind! &fd3 (new-state 0))
!(push-frame &fd3)
; Add multiple entries at level 1 using workflow functions
!(add_v &kb3 x 1)
!(add_v &kb3 y 1)
!(add_d &kb3 (x y) 1)
!(test (matchc &kb3 (Var $v (FSDepth 1) (Type "$v")) $v) (x y))
; Pop should remove all level 1 entries
!(pop-frame &kb3 &fd3)
!(test (matchc &kb3 (Var $v (FSDepth 1) (Type "$v")) $v) ())
!(test (matchc &kb3 (DVar $p (FSDepth 1) (Type "$d")) $p) ())

!(println! "Test 4: pop-frame preserves lower levels (using workflow functions)")
!(bind! &kb4 (new-space))
!(bind! &fd4 (new-state 0))
; Add at level 0 using workflow function
!(add_v &kb4 a 0)
!(push-frame &fd4)
; Add at level 1 using workflow function
!(add_v &kb4 b 1)
!(push-frame &fd4)
; Add at level 2 using workflow function
!(add_v &kb4 c 2)
; Pop level 2
!(pop-frame &kb4 &fd4)
; Level 0 and 1 should remain
!(test (matchc &kb4 (Var a (FSDepth 0) (Type "$v")) a) (a))
!(test (matchc &kb4 (Var b (FSDepth 1) (Type "$v")) b) (b))
!(test (matchc &kb4 (Var c (FSDepth 2) (Type "$v")) c) ())

!(println! "Test 5: pop-frame decrements frame depth")
!(bind! &kb5 (new-space))
!(bind! &fd5 (new-state 0))
!(test (get-state &fd5) 0)
!(push-frame &fd5)
!(test (get-state &fd5) 1)
!(push-frame &fd5)
!(test (get-state &fd5) 2)
!(pop-frame &kb5 &fd5)
!(test (get-state &fd5) 1)
!(pop-frame &kb5 &fd5)
!(test (get-state &fd5) 0)

!(println! "Test 6: Multiple push/pop sequence")
!(bind! &kb6 (new-space))
!(bind! &fd6 (new-state 0))
; Level 0: constant
!(add-atom &kb6 (Constant "0" (Type "$c")))
; Level 1: variable x
!(push-frame &fd6)
!(add-atom &kb6 (Var "x" (FSDepth 1) (Type "$v")))
; Level 2: variable y
!(push-frame &fd6)
!(add-atom &kb6 (Var "y" (FSDepth 2) (Type "$v")))
; Pop level 2
!(pop-frame &kb6 &fd6)
!(test (matchc &kb6 (Var "y" (FSDepth 2) (Type "$v")) "y") ())
!(test (matchc &kb6 (Var "x" (FSDepth 1) (Type "$v")) "x") ("x"))
; Pop level 1
!(pop-frame &kb6 &fd6)
!(test (matchc &kb6 (Var "x" (FSDepth 1) (Type "$v")) "x") ())
; Constant at level 0 should remain
!(test (matchc &kb6 (Constant "0" (Type "$c")) "0") ("0"))

!(println! "Test 7: pop-frame with hypotheses")
!(bind! &kb7 (new-space))
!(bind! &fd7 (new-state 0))
!(push-frame &fd7)
; Add floating hypothesis at level 1
!(add-atom &kb7 ((Label "tt") FHyp (FSDepth 1) ((Typecode "term") (FVar "t") (Type "$f"))))
!(add-atom &kb7 (FList (FSDepth 1) (("term" "t"))))
; Add essential hypothesis at level 1
!(add-atom &kb7 ((Label "min") EHyp (FSDepth 1) ((Statement ("|-" "P")) (Type "$e"))))
!(add-atom &kb7 (EList (FSDepth 1) (("|-" "P"))))
; Verify they exist
!(test (matchc &kb7 ((Label $l) FHyp (FSDepth 1) $d) $l) ("tt"))
!(test (matchc &kb7 ((Label $l) EHyp (FSDepth 1) $d) $l) ("min"))
; Pop should remove them
!(pop-frame &kb7 &fd7)
!(test (matchc &kb7 ((Label $l) FHyp (FSDepth 1) $d) $l) ())
!(test (matchc &kb7 ((Label $l) EHyp (FSDepth 1) $d) $l) ())
!(test (matchc &kb7 (FList (FSDepth 1) $f) $f) ())
!(test (matchc &kb7 (EList (FSDepth 1) $e) $e) ())

!(println! "Test 8: pop-frame with assertions")
!(bind! &kb8 (new-space))
!(bind! &fd8 (new-state 0))
!(push-frame &fd8)
; Add assertion at level 1
!(add-atom &kb8 ((Label "ax1") Assertion (FSDepth 1) ((DVars ()) (FHyps ()) (EHyps ()) (Statement ("|-" "P")) (Type "$a"))))
!(test (matchc &kb8 ((Label "ax1") Assertion (FSDepth 1) $d) "ax1") ("ax1"))
; Pop should remove it
!(pop-frame &kb8 &fd8)
!(test (matchc &kb8 ((Label "ax1") Assertion (FSDepth 1) $d) $l) ())

!(println! "")
!(println! "=== All pop-frame tests complete ===")
