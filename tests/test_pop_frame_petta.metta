!(import! &self ../mmverify-utils_petta)

!(println! "=== pop-frame Tests (New-Space API) ===")
!(println! "")

!(println! "Test 1: pop-frame removes entries at current level")
!(bind! &kb1 (new-space))
!(bind! &fd1 (new-state 0))
!(push-frame &fd1)
; Add variables at level 1
!(add_v &kb1 "x" 1)
!(add_v &kb1 "y" 1)
!(test (match &kb1 (Var "x" (FSDepth 1) (Type "$v")) found) found)
!(test (match &kb1 (Var "y" (FSDepth 1) (Type "$v")) found) found)
; Pop should remove them
!(pop-frame &kb1 &fd1)
!(test (collapse (match &kb1 (Var "x" (FSDepth 1) (Type "$v")) found)) ())
!(test (collapse (match &kb1 (Var "y" (FSDepth 1) (Type "$v")) found)) ())

!(println! "Test 2: pop-frame removes DV constraints at current level")
!(bind! &kb2 (new-space))
!(bind! &fd2 (new-state 0))
!(push-frame &fd2)
!(add_v &kb2 "a" 1)
!(add_v &kb2 "b" 1)
!(add_d &kb2 ("a" "b") 1)
!(test (match &kb2 (DVar ("a" "b") (FSDepth 1) (Type "$d")) found) found)
; Pop should remove DV constraint
!(pop-frame &kb2 &fd2)
!(test (collapse (match &kb2 (DVar ("a" "b") (FSDepth 1) (Type "$d")) found)) ())

!(println! "Test 3: pop-frame preserves lower levels")
!(bind! &kb3 (new-space))
!(bind! &fd3 (new-state 0))
; Add at level 0
!(add_v &kb3 "x" 0)
!(push-frame &fd3)
; Add at level 1
!(add_v &kb3 "y" 1)
!(push-frame &fd3)
; Add at level 2
!(add_v &kb3 "z" 2)
; Pop level 2
!(pop-frame &kb3 &fd3)
; Level 0 and 1 should remain
!(test (match &kb3 (Var "x" (FSDepth 0) (Type "$v")) found) found)
!(test (match &kb3 (Var "y" (FSDepth 1) (Type "$v")) found) found)
!(test (collapse (match &kb3 (Var "z" (FSDepth 2) (Type "$v")) found)) ())

!(println! "Test 4: pop-frame decrements frame depth")
!(bind! &kb4 (new-space))
!(bind! &fd4 (new-state 0))
!(test (get-state &fd4) 0)
!(push-frame &fd4)
!(test (get-state &fd4) 1)
!(push-frame &fd4)
!(test (get-state &fd4) 2)
!(pop-frame &kb4 &fd4)
!(test (get-state &fd4) 1)
!(pop-frame &kb4 &fd4)
!(test (get-state &fd4) 0)

!(println! "Test 5: Multiple push/pop sequence")
!(bind! &kb5 (new-space))
!(bind! &fd5 (new-state 0))
; Level 0: constant
!(add_c &kb5 "0")
; Level 1: variable x
!(push-frame &fd5)
!(add_v &kb5 "x" 1)
; Level 2: variable y
!(push-frame &fd5)
!(add_v &kb5 "y" 2)
; Pop level 2
!(pop-frame &kb5 &fd5)
!(test (collapse (match &kb5 (Var "y" (FSDepth 2) (Type "$v")) found)) ())
!(test (match &kb5 (Var "x" (FSDepth 1) (Type "$v")) found) found)
; Pop level 1
!(pop-frame &kb5 &fd5)
!(test (collapse (match &kb5 (Var "x" (FSDepth 1) (Type "$v")) found)) ())
; Constant at level 0 should remain
!(test (match &kb5 (Constant "0" (Type "$c")) found) found)

!(println! "Test 6: pop-frame with floating hypotheses")
!(bind! &kb6 (new-space))
!(bind! &fd6 (new-state 0))
!(push-frame &fd6)
!(add_c &kb6 "term")
!(add_v &kb6 "t" 1)
!(add_f &kb6 "tt" "term" "t" 1)
; Verify FHyp and FList exist
!(test (match &kb6 ((Label "tt") FHyp (FSDepth 1) $d) found) found)
!(test (match &kb6 (FList (FSDepth 1) $f) found) found)
; Pop should remove them
!(pop-frame &kb6 &fd6)
!(test (collapse (match &kb6 ((Label "tt") FHyp (FSDepth 1) $d) found)) ())
!(test (collapse (match &kb6 (FList (FSDepth 1) $f) found)) ())

!(println! "Test 7: pop-frame with essential hypotheses")
!(bind! &kb7 (new-space))
!(bind! &fd7 (new-state 0))
!(push-frame &fd7)
!(add_e &kb7 "min" ("|-" "P") 1)
; Verify EHyp and EList exist
!(test (match &kb7 ((Label "min") EHyp (FSDepth 1) $d) found) found)
!(test (match &kb7 (EList (FSDepth 1) $e) found) found)
; Pop should remove them
!(pop-frame &kb7 &fd7)
!(test (collapse (match &kb7 ((Label "min") EHyp (FSDepth 1) $d) found)) ())
!(test (collapse (match &kb7 (EList (FSDepth 1) $e) found)) ())

!(println! "")
!(println! "=== All pop-frame tests complete ✅ ===")
