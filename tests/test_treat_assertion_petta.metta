; PeTTa version of treat_assertion test suite (new-space style)
!(import! &self ../mmverify-utils_petta)

!(println! "=== treat_assertion Tests (PeTTa) ===")
!(println! "")

!(println! "Test 1: tze - assertion with no hypotheses")
!(bind! &tasp1 (new-state 1))
; Initial stack: ((Num 0) ("term" "t"))
!(add-atom &tast1 ((Num 0) ("term" "t")))
; tze: no DVars, no FHyps, no EHyps, Statement: ("term" "0")
!(treat_assertion &takb1 &tast1 &tasp1 "tze"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ("term" "0")) (Type "$a")) 1)
!(test (collapse (match &tast1 ((Num 1) $entry) $entry)) (("term" "0")))
!(test (get-state &tasp1) 1)

!(println! "Test 2: tpl - assertion with two FHyps (mini proof trace)")
!(bind! &tasp2 (new-state 0))
; Mini proof trace: build stack using treat_hypothesis
!(add-atom &takb2 (ActiveHyp "vt"))
!(treat_hypothesis &takb2 &tast2 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Manually add second argument ("0" constant)
!(add-atom &tast2 ((Num 1) ("term" "0")))
; tpl: FHyps: (("term" "t") ("term" "r")), Statement: ("term" "(" "t" "+" "r" ")")
!(treat_assertion &takb2 &tast2 &tasp2 "tpl"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 2)
!(test (collapse (match &tast2 ((Num 0) $entry) $entry)) (("term" "(" "t" "+" "0" ")")))
!(test (get-state &tasp2) 2)

!(println! "Test 3: weq - assertion with two FHyps producing wff")
!(bind! &tasp3 (new-state 2))
; Initial stack
!(add-atom &tast3 ((Num 0) ("term" "(" "t" "+" "0" ")")))
!(add-atom &tast3 ((Num 1) ("term" "t")))
; weq: FHyps: (("term" "t") ("term" "r")), Statement: ("wff" "t" "=" "r")
!(treat_assertion &takb3 &tast3 &tasp3 "weq"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("wff" "t" "=" "r")) (Type "$a")) 2)
!(test (collapse (match &tast3 ((Num 0) $entry) $entry)) (("wff" "(" "t" "+" "0" ")" "=" "t")))
!(test (get-state &tasp3) 2)

!(println! "Test 4: a2 - assertion with one FHyp producing |- statement")
!(bind! &tasp4 (new-state 0))
; Previous assertion results
!(add-atom &tast4 ((Num 0) ("wff" "(" "t" "+" "0" ")" "=" "t")))
!(add-atom &tast4 ((Num 1) ("wff" "t" "=" "t")))
; Build floating hypothesis
!(add-atom &takb4 (ActiveHyp "vt"))
!(treat_hypothesis &takb4 &tast4 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 2)
; a2: FHyps: (("term" "t")), Statement: ("|-" "(" "t" "+" "0" ")" "=" "t")
!(treat_assertion &takb4 &tast4 &tasp4 "a2"
  ((DVars ()) (FHyps (("term" "t"))) (EHyps ()) (Statement ("|-" "(" "t" "+" "0" ")" "=" "t")) (Type "$a")) 3)
!(test (collapse (match &tast4 ((Num 2) $entry) $entry)) (("|-" "(" "t" "+" "0" ")" "=" "t")))
!(test (get-state &tasp4) 3)

!(println! "Test 5: Complex substitution - multiple variables")
!(bind! &tasp5 (new-state 0))
; Build all three floating hypotheses
!(add-atom &takb5 (ActiveHyp "vx"))
!(add-atom &takb5 (ActiveHyp "vy"))
!(add-atom &takb5 (ActiveHyp "vz"))
!(treat_hypothesis &takb5 &tast5 "vx" FHyp ((Typecode "term") (FVar "x") (Type "$f")) 0)
!(treat_hypothesis &takb5 &tast5 "vy" FHyp ((Typecode "term") (FVar "y") (Type "$f")) 1)
!(treat_hypothesis &takb5 &tast5 "vz" FHyp ((Typecode "term") (FVar "z") (Type "$f")) 2)
; Assertion with 3 FHyps
!(treat_assertion &takb5 &tast5 &tasp5 "test"
  ((DVars ()) (FHyps (("term" "a") ("term" "b") ("term" "c"))) (EHyps ())
   (Statement ("term" "(" "a" "+" "(" "b" "*" "c" ")" ")")) (Type "$a")) 3)
!(test (collapse (match &tast5 ((Num 0) $entry) $entry)) (("term" "(" "x" "+" "(" "y" "*" "z" ")" ")")))
!(test (get-state &tasp5) 3)

!(println! "Test 6: Error - stack underflow")
!(bind! &tasp6 (new-state 0))
; Build only one floating hypothesis
!(add-atom &takb6 (ActiveHyp "vt"))
!(treat_hypothesis &takb6 &tast6 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Try assertion requiring 2 FHyps but only 1 on stack
!(test (treat_assertion &takb6 &tast6 &tasp6 "bad"
    ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 1)
  (Error ((label "bad") (npop 2)) "Stack underflow: proof step requires too many hypotheses"))

!(println! "Test 7: Assertion with EHyp verification (mp)")
!(bind! &tasp7 (new-state 0))
; Build floating hypotheses
!(add-atom &takb7 (ActiveHyp "vP"))
!(add-atom &takb7 (ActiveHyp "vQ"))
!(treat_hypothesis &takb7 &tast7 "vP" FHyp ((Typecode "wff") (FVar "P") (Type "$f")) 0)
!(treat_hypothesis &takb7 &tast7 "vQ" FHyp ((Typecode "wff") (FVar "Q") (Type "$f")) 1)
; Build essential hypotheses
!(add-atom &takb7 (ActiveHyp "min"))
!(add-atom &takb7 (ActiveHyp "maj"))
!(treat_hypothesis &takb7 &tast7 "min" EHyp ((Statement ("|-" "P")) (Type "$e")) 2)
!(treat_hypothesis &takb7 &tast7 "maj" EHyp ((Statement ("|-" "(" "P" "->" "Q" ")")) (Type "$e")) 3)
; mp assertion
!(treat_assertion &takb7 &tast7 &tasp7 "mp"
  ((DVars ()) (FHyps (("wff" "P") ("wff" "Q"))) (EHyps (("|-" "P") ("|-" "(" "P" "->" "Q" ")")))
   (Statement ("|-" "Q")) (Type "$a")) 4)
!(test (collapse (match &tast7 ((Num 0) $entry) $entry)) (("|-" "Q")))
!(test (get-state &tasp7) 4)

!(println! "Test 8: Realistic scenario - building up proof stack")
!(bind! &tasp8 (new-state 0))
; Start with floating hypothesis
!(add-atom &takb8 (ActiveHyp "vt"))
!(treat_hypothesis &takb8 &tast8 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Apply tze
!(treat_assertion &takb8 &tast8 &tasp8 "tze"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ("term" "0")) (Type "$a")) 1)
!(test (get-state &tasp8) 1)
; Apply tpl
!(treat_assertion &takb8 &tast8 &tasp8 "tpl"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 2)
!(test (collapse (match &tast8 ((Num 0) $entry) $entry)) (("term" "(" "t" "+" "0" ")")))
!(test (get-state &tasp8) 2)

!(println! "Test 9: npop calculation with both FHyps and EHyps")
!(bind! &tasp9 (new-state 0))
; Build 3 floating hypotheses
!(add-atom &takb9 (ActiveHyp "vA"))
!(add-atom &takb9 (ActiveHyp "vB"))
!(add-atom &takb9 (ActiveHyp "vC"))
!(treat_hypothesis &takb9 &tast9 "vA" FHyp ((Typecode "wff") (FVar "A") (Type "$f")) 0)
!(treat_hypothesis &takb9 &tast9 "vB" FHyp ((Typecode "wff") (FVar "B") (Type "$f")) 1)
!(treat_hypothesis &takb9 &tast9 "vC" FHyp ((Typecode "wff") (FVar "C") (Type "$f")) 2)
; Build 2 essential hypotheses
!(add-atom &takb9 (ActiveHyp "hypA"))
!(add-atom &takb9 (ActiveHyp "hypB"))
!(treat_hypothesis &takb9 &tast9 "hypA" EHyp ((Statement ("|-" "A")) (Type "$e")) 3)
!(treat_hypothesis &takb9 &tast9 "hypB" EHyp ((Statement ("|-" "B")) (Type "$e")) 4)
; Assertion with 3 FHyps and 2 EHyps (npop = 5)
!(treat_assertion &takb9 &tast9 &tasp9 "complex"
  ((DVars ()) (FHyps (("wff" "x") ("wff" "y") ("wff" "z")))
   (EHyps (("|-" "x") ("|-" "y")))
   (Statement ("|-" "(" "x" "&" "y" "&" "z" ")")) (Type "$a")) 5)
!(test (collapse (match &tast9 ((Num 0) $entry) $entry)) (("|-" "(" "A" "&" "B" "&" "C" ")")))
!(test (get-state &tasp9) 5)

!(println! "Test 10: Empty statement result")
!(bind! &tasp10 (new-state 0))
; Assertion with no FHyps/EHyps and empty statement
!(treat_assertion &takb10 &tast10 &tasp10 "empty"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ()) (Type "$a")) 0)
!(test (collapse (match &tast10 ((Num 0) $entry) $entry)) (()))
!(test (get-state &tasp10) 0)

!(println! "")
!(println! "=== All treat_assertion tests complete ===")
