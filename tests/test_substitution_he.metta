; Unit tests for substitution functions from mmverify-utils.metta
; Tests: apply_subst_tok, add-subst, check_subst
;
; NOTE: Full apply_subst testing requires Metamath statements as quoted string lists
; (e.g., ("term" "t" "+" "r")) to keep object language separate from meta-language.
; These tests focus on the core token-level operations.

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== Substitution Function Tests ===")
!(println! "")

!(println! "Test 1: apply_subst_tok - No substitution")
!(bind! &subst1 (new-space))
; Token 'x' has no substitution, should return 'x' unchanged
!(test (apply_subst_tok &subst1 x) x)

!(println! "Test 2: apply_subst_tok - Simple substitution")
!(bind! &subst2 (new-space))
!(add-atom &subst2 (x 5))
; Token 'x' maps to 5
!(test (apply_subst_tok &subst2 x) 5)

!(println! "Test 3: apply_subst_tok - Variable to expression substitution")
!(bind! &subst3 (new-space))
!(add-atom &subst3 (t ("0")))
; Token 't' maps to expression ("0")
!(test (apply_subst_tok &subst3 t) ("0"))

!(println! "Test 4: apply_subst_tok - Non-matching token")
!(bind! &subst4 (new-space))
!(add-atom &subst4 (x 5))
; Token 'y' has no substitution
!(test (apply_subst_tok &subst4 y) y)

!(println! "Test 5: add-subst - Matching typecode")
!(bind! &stack5 (new-space))
!(bind! &subst5 (new-space))
!(bind! &sp5 (new-state 0))
!(add-atom &stack5 ((Num 0) ("term" "0")))
; Stack has ("term" "0") at position 0, f-hyp is ("term" "t")
; decons-atom splits to head="term" and tail=("0")
; Should add ("t" ("0")) to subst and return ("t" ("0"))
!(test (add-subst &stack5 &sp5 &subst5 ("term" "t")) ("t" ("0")))

!(println! "Test 6: add-subst - Type mismatch error")
!(bind! &stack6 (new-space))
!(bind! &subst6 (new-space))
!(bind! &sp6 (new-state 0))
!(add-atom &stack6 ((Num 0) ("wff" "P")))
; Stack has ("wff" "P") at position 0, but f-hyp expects ("term" "t")
; Should return Error
!(assertEqualToResult (add-subst &stack6 &sp6 &subst6 ("term" "t"))
  ((Error ((sp 0) (entry ("wff" "P")) (typecode "term") (var "t")) "Proof stack entry does not match floating hypothesis.")))

!(println! "Test 7: add-subst - With complex expression substitution")
!(bind! &stack7 (new-space))
!(bind! &subst7 (new-space))
!(bind! &sp7 (new-state 0))
!(add-atom &stack7 ((Num 0) ("wff" "P" "->" "Q")))
; Stack has ("wff" "P" "->" "Q") at position 0, f-hyp is ("wff" "ps")
; decons-atom splits to head="wff" and tail=("P" "->" "Q")
; Should return ("ps" ("P" "->" "Q"))
!(test (add-subst &stack7 &sp7 &subst7 ("wff" "ps")) ("ps" ("P" "->" "Q")))

!(println! "Test 8: add-subst - Variable name in error")
!(bind! &stack8 (new-space))
!(bind! &subst8 (new-space))
!(bind! &sp8 (new-state 0))
!(add-atom &stack8 ((Num 0) ("class" "A")))
; Stack has ("class" "A") but f-hyp expects ("setvar" "x")
; Error should show correct var name in error
!(assertEqualToResult (add-subst &stack8 &sp8 &subst8 ("setvar" "x"))
  ((Error ((sp 0) (entry ("class" "A")) (typecode "setvar") (var "x")) "Proof stack entry does not match floating hypothesis.")))

!(println! "")
!(println! "=== All substitution tests complete ===")
!(println! "")
!(println! "NOTE: For comprehensive apply_subst and check_subst tests,")
!(println! "see test_substitution_full.metta (12 additional tests)")
