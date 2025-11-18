; Unit tests for treat_assertion function
; treat_assertion processes assertions ($a and $p) during proof verification
; Using real-world examples from demo0.mm verification

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== treat_assertion Tests ===")
!(println! "")

!(println! "Test 1: tze - assertion with no hypotheses")
!(bind! &kb1 (new-space))
!(bind! &stack1 (new-space))
!(bind! &sp1 (new-state 1.0))
; Initial stack: ((Num 0) ("term" "t"))
!(add-atom &stack1 ((Num 0) ("term" "t")))
; tze: no DVars, no FHyps, no EHyps, Statement: ("term" "0")
!(treat_assertion &kb1 &stack1 &sp1 "tze"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ("term" "0")) (Type "$a")) 1.0)
!(test (match &stack1 ((Num 1.0) $entry) $entry) ("term" "0"))
!(test (get-state &sp1) 1.0)

!(println! "Test 2: tpl - assertion with two FHyps (mini proof trace)")
!(bind! &kb2 (new-space))
!(bind! &stack2 (new-space))
!(bind! &sp2 (new-state 0.0))
; Mini proof trace: build stack using treat_hypothesis with QUOTED strings
!(add-atom &kb2 (ActiveHyp "vt"))
!(treat_hypothesis &kb2 &stack2 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Manually add second argument ("0" constant)
!(add-atom &stack2 ((Num 1) ("term" "0")))
; tpl: FHyps: (("term" "t") ("term" "r")), Statement: ("term" "(" "t" "+" "r" ")")
; sp_val = stack_len - npop = 2 - 2 = 0, then add-subst increments sp twice → final sp = 2.0
!(treat_assertion &kb2 &stack2 &sp2 "tpl"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 2.0)
!(test (match &stack2 ((Num 0) $entry) $entry) ("term" "(" "t" "+" "0" ")"))
!(test (get-state &sp2) 2.0)

!(println! "Test 3: weq - assertion with two FHyps producing wff")
!(bind! &kb3 (new-space))
!(bind! &stack3 (new-space))
!(bind! &sp3 (new-state 2.0))
; Initial stack: ((Num 0) ("term" "(" "t" "+" "0" ")")) ((Num 1) ("term" "t"))
!(add-atom &stack3 ((Num 0) ("term" "(" "t" "+" "0" ")")))
!(add-atom &stack3 ((Num 1) ("term" "t")))
; weq: FHyps: (("term" "t") ("term" "r")), Statement: ("wff" "t" "=" "r")
!(treat_assertion &kb3 &stack3 &sp3 "weq"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("wff" "t" "=" "r")) (Type "$a")) 2.0)
!(test (match &stack3 ((Num 0) $entry) $entry) ("wff" "(" "t" "+" "0" ")" "=" "t"))
!(test (get-state &sp3) 2.0)  ; sp_val=0, then add-subst increments twice → final sp = 2.0

!(println! "Test 4: a2 - assertion with one FHyp producing |- statement")
!(bind! &kb4 (new-space))
!(bind! &stack4 (new-space))
!(bind! &sp4 (new-state 0.0))
; Previous assertion results (manual)
!(add-atom &stack4 ((Num 0) ("wff" "(" "t" "+" "0" ")" "=" "t")))
!(add-atom &stack4 ((Num 1) ("wff" "t" "=" "t")))
; Build floating hypothesis using treat_hypothesis (realistic!)
!(add-atom &kb4 (ActiveHyp "vt"))
!(treat_hypothesis &kb4 &stack4 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 2)
; a2: FHyps: (("term" "t")), Statement: ("|-" "(" "t" "+" "0" ")" "=" "t")
!(treat_assertion &kb4 &stack4 &sp4 "a2"
  ((DVars ()) (FHyps (("term" "t"))) (EHyps ()) (Statement ("|-" "(" "t" "+" "0" ")" "=" "t")) (Type "$a")) 3.0)
!(test (match &stack4 ((Num 2.0) $entry) $entry) ("|-" "(" "t" "+" "0" ")" "=" "t"))
!(test (get-state &sp4) 3.0)  ; sp_val=2, then add-subst increments once → final sp = 3.0

!(println! "Test 5: Complex substitution - multiple variables")
!(bind! &kb5 (new-space))
!(bind! &stack5 (new-space))
!(bind! &sp5 (new-state 0.0))
; Build all three floating hypotheses using treat_hypothesis (realistic!)
!(add-atom &kb5 (ActiveHyp "vx"))
!(add-atom &kb5 (ActiveHyp "vy"))
!(add-atom &kb5 (ActiveHyp "vz"))
!(treat_hypothesis &kb5 &stack5 "vx" FHyp ((Typecode "term") (FVar "x") (Type "$f")) 0)
!(treat_hypothesis &kb5 &stack5 "vy" FHyp ((Typecode "term") (FVar "y") (Type "$f")) 1)
!(treat_hypothesis &kb5 &stack5 "vz" FHyp ((Typecode "term") (FVar "z") (Type "$f")) 2)
; Assertion with 3 FHyps creating complex expression
!(treat_assertion &kb5 &stack5 &sp5 "test"
  ((DVars ()) (FHyps (("term" "a") ("term" "b") ("term" "c"))) (EHyps ())
   (Statement ("term" "(" "a" "+" "(" "b" "*" "c" ")" ")")) (Type "$a")) 3.0)
!(test (match &stack5 ((Num 0) $entry) $entry) ("term" "(" "x" "+" "(" "y" "*" "z" ")" ")"))
!(test (get-state &sp5) 3.0)  ; sp_val=0, then add-subst increments 3 times → final sp = 3.0

!(println! "Test 6: Error - stack underflow")
!(bind! &kb6 (new-space))
!(bind! &stack6 (new-space))
!(bind! &sp6 (new-state 0.0))
; Build only one floating hypothesis using treat_hypothesis
!(add-atom &kb6 (ActiveHyp "vt"))
!(treat_hypothesis &kb6 &stack6 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Try assertion requiring 2 FHyps but only 1 on stack
!(assertEqualToResult
  (treat_assertion &kb6 &stack6 &sp6 "bad"
    ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 1.0)
  ((Error ((label "bad") (npop 2)) "Stack underflow: proof step requires too many hypotheses")))

!(println! "Test 7: Assertion with EHyp verification (mp)")
!(bind! &kb7 (new-space))
!(bind! &stack7 (new-space))
!(bind! &sp7 (new-state 0.0))
; Build floating hypotheses using treat_hypothesis (realistic!)
!(add-atom &kb7 (ActiveHyp "vP"))
!(add-atom &kb7 (ActiveHyp "vQ"))
!(treat_hypothesis &kb7 &stack7 "vP" FHyp ((Typecode "wff") (FVar "P") (Type "$f")) 0)
!(treat_hypothesis &kb7 &stack7 "vQ" FHyp ((Typecode "wff") (FVar "Q") (Type "$f")) 1)
; Build essential hypotheses using treat_hypothesis (realistic!)
!(add-atom &kb7 (ActiveHyp "min"))
!(add-atom &kb7 (ActiveHyp "maj"))
!(treat_hypothesis &kb7 &stack7 "min" EHyp ((Statement ("|-" "P")) (Type "$e")) 2)
!(treat_hypothesis &kb7 &stack7 "maj" EHyp ((Statement ("|-" "(" "P" "->" "Q" ")")) (Type "$e")) 3)
; mp: FHyps: (("wff" "P") ("wff" "Q")), EHyps: (("|-" "P") ("|-" "(" "P" "->" "Q" ")"))), Statement: ("|-" "Q")
!(treat_assertion &kb7 &stack7 &sp7 "mp"
  ((DVars ()) (FHyps (("wff" "P") ("wff" "Q"))) (EHyps (("|-" "P") ("|-" "(" "P" "->" "Q" ")")))
   (Statement ("|-" "Q")) (Type "$a")) 4.0)
!(test (match &stack7 ((Num 0) $entry) $entry) ("|-" "Q"))
!(test (get-state &sp7) 4.0)  ; sp_val=0, add-subst increments 2x, check_subst increments 2x → final sp = 4.0

!(println! "Test 8: Realistic scenario - building up proof stack")
!(bind! &kb8 (new-space))
!(bind! &stack8 (new-space))
!(bind! &sp8 (new-state 0.0))
; Start with floating hypothesis using treat_hypothesis (realistic!)
!(add-atom &kb8 (ActiveHyp "vt"))
!(treat_hypothesis &kb8 &stack8 "vt" FHyp ((Typecode "term") (FVar "t") (Type "$f")) 0)
; Apply tze
!(treat_assertion &kb8 &stack8 &sp8 "tze"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ("term" "0")) (Type "$a")) 1.0)
!(test (get-state &sp8) 1.0)
; Apply tpl (stack_len is now 2 after tze added entry)
!(treat_assertion &kb8 &stack8 &sp8 "tpl"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 2.0)
!(test (match &stack8 ((Num 0) $entry) $entry) ("term" "(" "t" "+" "0" ")"))
!(test (get-state &sp8) 2.0)  ; After tpl: sp_val=0, add-subst increments 2x → final sp = 2.0

!(println! "Test 9: npop calculation with both FHyps and EHyps")
!(bind! &kb9 (new-space))
!(bind! &stack9 (new-space))
!(bind! &sp9 (new-state 0.0))
; Build 3 floating hypotheses using treat_hypothesis (realistic!)
!(add-atom &kb9 (ActiveHyp "vA"))
!(add-atom &kb9 (ActiveHyp "vB"))
!(add-atom &kb9 (ActiveHyp "vC"))
!(treat_hypothesis &kb9 &stack9 "vA" FHyp ((Typecode "wff") (FVar "A") (Type "$f")) 0)
!(treat_hypothesis &kb9 &stack9 "vB" FHyp ((Typecode "wff") (FVar "B") (Type "$f")) 1)
!(treat_hypothesis &kb9 &stack9 "vC" FHyp ((Typecode "wff") (FVar "C") (Type "$f")) 2)
; Build 2 essential hypotheses using treat_hypothesis (realistic!)
!(add-atom &kb9 (ActiveHyp "hypA"))
!(add-atom &kb9 (ActiveHyp "hypB"))
!(treat_hypothesis &kb9 &stack9 "hypA" EHyp ((Statement ("|-" "A")) (Type "$e")) 3)
!(treat_hypothesis &kb9 &stack9 "hypB" EHyp ((Statement ("|-" "B")) (Type "$e")) 4)
; Assertion with 3 FHyps and 2 EHyps (npop = 5)
!(treat_assertion &kb9 &stack9 &sp9 "complex"
  ((DVars ()) (FHyps (("wff" "x") ("wff" "y") ("wff" "z")))
   (EHyps (("|-" "x") ("|-" "y")))
   (Statement ("|-" "(" "x" "&" "y" "&" "z" ")")) (Type "$a")) 5.0)
!(test (match &stack9 ((Num 0) $entry) $entry) ("|-" "(" "A" "&" "B" "&" "C" ")"))
!(test (get-state &sp9) 5.0)  ; sp_val=0, add-subst 3x, check_subst 2x → final sp = 5.0

!(println! "Test 10: Empty statement result")
!(bind! &kb10 (new-space))
!(bind! &stack10 (new-space))
!(bind! &sp10 (new-state 0.0))
; Assertion with no FHyps/EHyps and empty statement
!(treat_assertion &kb10 &stack10 &sp10 "empty"
  ((DVars ()) (FHyps ()) (EHyps ()) (Statement ()) (Type "$a")) 0.0)
!(test (match &stack10 ((Num 0) $entry) $entry) ())
!(test (get-state &sp10) 0.0)

!(println! "")
!(println! "=== All treat_assertion tests complete ===")
