; Unit tests for treat_hypothesis function
; treat_hypothesis processes $f and $e hypotheses during proof verification
; Using parameterized version from mmverify-utils.metta

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== treat_hypothesis Tests ===")
!(println! "")

!(println! "Test 1: Process FHyp (floating hypothesis)")
!(bind! &kb1 (new-space))
!(bind! &stack1 (new-space))
!(add-atom &kb1 (ActiveHyp "tt"))
!(treat_hypothesis &kb1 &stack1 "tt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
!(test (match &stack1 ((Num 0) $entry) $entry) ("term" "t"))

!(println! "Test 2: Process EHyp (essential hypothesis)")
!(bind! &kb2 (new-space))
!(bind! &stack2 (new-space))
!(add-atom &kb2 (ActiveHyp "min"))
!(treat_hypothesis &kb2 &stack2 "min" EHyp ((Statement ("|-" "P")) (Type "$e")) 0)
!(test (match &stack2 ((Num 0) $entry) $entry) ("|-" "P"))

!(println! "Test 3: Multiple FHyps at different stack positions")
!(bind! &kb3 (new-space))
!(bind! &stack3 (new-space))
!(add-atom &kb3 (ActiveHyp "tt"))
!(add-atom &kb3 (ActiveHyp "tr"))
!(treat_hypothesis &kb3 &stack3 "tt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
!(treat_hypothesis &kb3 &stack3 "tr" FHyp ((Typecode "term") (FVar "r") (Type "$f")) 1)
!(test (match &stack3 ((Num 0) $entry) $entry) ("term" "t"))
!(test (match &stack3 ((Num 1) $entry) $entry) ("term" "r"))

!(println! "Test 4: Error - hypothesis not active")
!(bind! &kb4 (new-space))
!(bind! &stack4 (new-space))
!(assertEqualToResult (treat_hypothesis &kb4 &stack4 "bad" FHyp ((Typecode "wff") (FVar "P") (Type "$f")) 0)
  ((Error (label "bad") "The label is the label of a nonactive hypothesis.")))

!(println! "Test 5: FHyp with wff typecode")
!(bind! &kb5 (new-space))
!(bind! &stack5 (new-space))
!(add-atom &kb5 (ActiveHyp "wp"))
!(treat_hypothesis &kb5 &stack5 "wp" FHyp ((Typecode "wff") (FVar "P") (Type "$f")) 0)
!(test (match &stack5 ((Num 0) $entry) $entry) ("wff" "P"))

!(println! "Test 6: EHyp with complex statement")
!(bind! &kb6 (new-space))
!(bind! &stack6 (new-space))
!(add-atom &kb6 (ActiveHyp "eq"))
!(treat_hypothesis &kb6 &stack6 "eq" EHyp ((Statement ("|-" "(" "t" "+" "0" ")" "=" "t")) (Type "$e")) 0)
!(test (match &stack6 ((Num 0) $entry) $entry) ("|-" "(" "t" "+" "0" ")" "=" "t"))

!(println! "Test 7: Stack positions accumulate correctly")
!(bind! &kb7 (new-space))
!(bind! &stack7 (new-space))
!(add-atom &kb7 (ActiveHyp "h1"))
!(add-atom &kb7 (ActiveHyp "h2"))
!(add-atom &kb7 (ActiveHyp "h3"))
!(treat_hypothesis &kb7 &stack7 "h1" FHyp ((Typecode "term") (FVar "x") (Type "$f")) 0)
!(treat_hypothesis &kb7 &stack7 "h2" EHyp ((Statement ("|-" "P")) (Type "$e")) 1)
!(treat_hypothesis &kb7 &stack7 "h3" FHyp ((Typecode "wff") (FVar "Q") (Type "$f")) 2)
!(test (matchc &stack7 ((Num $n) $entry) $n) (0 1 2))

!(println! "Test 8: Realistic scenario - multiple hypotheses for a theorem")
!(bind! &kb8 (new-space))
!(bind! &stack8 (new-space))
!(add-atom &kb8 (ActiveHyp "tt"))
!(add-atom &kb8 (ActiveHyp "tr"))
!(add-atom &kb8 (ActiveHyp "min"))
!(treat_hypothesis &kb8 &stack8 "tt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
!(treat_hypothesis &kb8 &stack8 "tr" FHyp ((Typecode "term") (FVar "r") (Type "$f")) 1)
!(treat_hypothesis &kb8 &stack8 "min" EHyp ((Statement ("|-" "t" "=" "r")) (Type "$e")) 2)
!(test (matchc &stack8 ((Num $n) $entry) ($n $entry))
       ((0 ("term" "t")) (1 ("term" "r")) (2 ("|-" "t" "=" "r"))))

!(println! "Test 9: Empty statement in EHyp")
!(bind! &kb9 (new-space))
!(bind! &stack9 (new-space))
!(add-atom &kb9 (ActiveHyp "empty"))
!(treat_hypothesis &kb9 &stack9 "empty" EHyp ((Statement ()) (Type "$e")) 0)
!(test (match &stack9 ((Num 0) $entry) $entry) ())

!(println! "Test 10: Different typecodes")
!(bind! &kb10 (new-space))
!(bind! &stack10 (new-space))
!(add-atom &kb10 (ActiveHyp "class"))
!(add-atom &kb10 (ActiveHyp "setvar"))
!(treat_hypothesis &kb10 &stack10 "class" FHyp ((Typecode "class") (FVar "A") (Type "$f")) 0)
!(treat_hypothesis &kb10 &stack10 "setvar" FHyp ((Typecode "setvar") (FVar "x") (Type "$f")) 1)
!(test (match &stack10 ((Num 0) $entry) $entry) ("class" "A"))
!(test (match &stack10 ((Num 1) $entry) $entry) ("setvar" "x"))

!(println! "")
!(println! "=== All treat_hypothesis tests complete ===")
