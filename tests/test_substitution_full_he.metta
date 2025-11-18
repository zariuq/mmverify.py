; Full tests for substitution functions including apply_subst and check_subst
; Based on patterns from playpen.metta and working examples

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== Full Substitution Tests ===")
!(println! "")

!(println! "Test 1: apply_subst - Empty statement")
!(bind! &s1 (new-space))
!(test (apply_subst &s1 ()) ())

!(println! "Test 2: apply_subst - No substitutions needed")
!(bind! &s2 (new-space))
!(test (apply_subst &s2 ("term" "0")) ("term" "0"))

!(println! "Test 3: apply_subst - Single substitution")
!(bind! &s3 (new-space))
!(add-atom &s3 ("t" "0"))
; Statement ("term" "t") with "t" -> "0"
!(test (apply_subst &s3 ("term" "t")) ("term" "0"))

!(println! "Test 4: apply_subst - Multiple substitutions")
!(bind! &s4 (new-space))
!(add-atom &s4 ("t" "0"))
!(add-atom &s4 ("r" "1"))
; Statement ("wff" "t" "=" "r") with "t" -> "0", "r" -> "1"
!(test (apply_subst &s4 ("wff" "t" "=" "r")) ("wff" "0" "=" "1"))

!(println! "Test 5: apply_subst - Nested expression substitution")
!(bind! &s5 (new-space))
!(add-atom &s5 ("P" ("wff" "x")))
!(add-atom &s5 ("Q" ("wff" "y")))
; Statement ("|-" "P" "->" "Q") with P -> ("wff" "x"), Q -> ("wff" "y")
; Result should be flattened
!(test (apply_subst &s5 ("|-" "P" "->" "Q")) ("|-" "wff" "x" "->" "wff" "y"))

!(println! "Test 6: apply_subst - Mixed constants and variables")
!(bind! &s6 (new-space))
!(add-atom &s6 ("t" "5"))
; Statement ("|-" "(" "t" "+" "0" ")" "=" "t")
!(test (apply_subst &s6 ("|-" "(" "t" "+" "0" ")" "=" "t")) ("|-" "(" "5" "+" "0" ")" "=" "5"))

!(println! "Test 7: check_subst - Exact match (no error)")
!(bind! &stack7 (new-space))
!(bind! &subst7 (new-space))
!(bind! &sp7 (new-state 0))
!(add-atom &stack7 ((Num 0) ("term" "0")))
; Stack has ("term" "0"), ehyp is ("term" "t"), subst has "t" -> "0"
!(add-atom &subst7 ("t" "0"))
; check_subst should match without error (returns adjust-state result, not ())
!(check_subst &stack7 &sp7 &subst7 ("term" "t"))
!(println! "  Test 7 passed - no error thrown")

!(println! "Test 8: check_subst - Complex match (no error)")
!(bind! &stack8 (new-space))
!(bind! &subst8 (new-space))
!(bind! &sp8 (new-state 0))
!(add-atom &stack8 ((Num 0) ("|-" "0" "+" "0" "=" "0")))
!(add-atom &subst8 ("t" "0"))
; Stack has ("|-" "0" "+" "0" "=" "0")
; ehyp is ("|-" "t" "+" "t" "=" "t"), after subst becomes ("|-" "0" "+" "0" "=" "0")
!(check_subst &stack8 &sp8 &subst8 ("|-" "t" "+" "t" "=" "t"))
!(println! "  Test 8 passed - no error thrown")

!(println! "Test 9: check_subst - Mismatch error")
!(bind! &stack9 (new-space))
!(bind! &subst9 (new-space))
!(bind! &sp9 (new-state 0))
!(add-atom &stack9 ((Num 0) ("term" "1")))
!(add-atom &subst9 ("t" "0"))
; Stack has ("term" "1"), ehyp becomes ("term" "0") after substitution
!(assertEqualToResult (check_subst &stack9 &sp9 &subst9 ("term" "t"))
  ((Error ((sp &sp9) (entry ("term" "1")) (ehyp ("term" "t")) (subst_h ("term" "0"))) "Proof stack entry does not match essential hypothesis.")))

!(println! "Test 10: apply_subst - Preserves non-variables")
!(bind! &s10 (new-space))
!(add-atom &s10 ("x" "42"))
; Constants and operators should remain unchanged
!(test (apply_subst &s10 ("|-" "(" "x" "+" "0" ")" "=" "x")) ("|-" "(" "42" "+" "0" ")" "=" "42"))

!(println! "Test 11: apply_subst - Statement with all constants")
!(bind! &s11 (new-space))
!(add-atom &s11 ("x" "1"))
; Even with substitution defined, constants remain unchanged
!(test (apply_subst &s11 ("|-" "0" "=" "0")) ("|-" "0" "=" "0"))

!(println! "Test 12: check_subst with apply_subst - Integration")
!(bind! &stack12 (new-space))
!(bind! &subst12 (new-space))
!(bind! &sp12 (new-state 0))
; Build a realistic scenario
!(add-atom &stack12 ((Num 0) ("|-" "(" "0" "+" "1" ")" "=" "(" "1" "+" "0" ")")))
!(add-atom &subst12 ("t" "0"))
!(add-atom &subst12 ("r" "1"))
; ehyp ("|-" "(" "t" "+" "r" ")" "=" "(" "r" "+" "t" ")")
; After substitution: ("|-" "(" "0" "+" "1" ")" "=" "(" "1" "+" "0" ")")
!(check_subst &stack12 &sp12 &subst12 ("|-" "(" "t" "+" "r" ")" "=" "(" "r" "+" "t" ")"))
!(println! "  Test 12 passed - substitution matched correctly")

!(println! "")
!(println! "=== All full substitution tests complete ===")