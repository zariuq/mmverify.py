; MeTTa version of add_a and make_assertion - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))


!(println! "=== Testing add_a and make_assertion ===")
!(println! "")

!(println! "Test 1: Simple assertion with no hypotheses")
!(bind! &kb1 (new-space))
!(add_a &kb1 ax1 (wff P))
!(assertEqual (match &kb1 ((Label $l) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) ($l $s))
              (ax1 (wff P)))

!(println! "Test 2: Assertion with floating hypothesis (x appears in statement)")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var x 0 (Type "$v")))
!(add-atom &kb2 (FList (FSDepth 1) (Cons (class x) Nil)))
; Statement includes x as a mandatory variable
!(add_a &kb2 ax2 (wff x))
!(assertEqual (match &kb2 ((Label ax2) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $fh)
              ((class x)))

!(println! "Test 3: Assertion with essential hypothesis")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (EList (FSDepth 1) (Cons (wff P) Nil)))
!(add_a &kb3 ax3 (wff (implies P Q)))
!(assertEqual (match &kb3 ((Label ax3) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $eh)
              ((wff P)))

!(println! "Test 4: Assertion with disjoint variables (x, y in statement)")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var x 0 (Type "$v")))
!(add-atom &kb4 (Var y 0 (Type "$v")))
!(add-atom &kb4 (DVar (x y) 1 (Type "$d")))
!(add-atom &kb4 (FList (FSDepth 1) (Cons (class x) (Cons (class y) Nil))))
; Statement must include x and y as tokens so they become mandatory vars
!(add_a &kb4 ax4 (wff x y))
; Note: match returns non-deterministic results including empties
!(assertEqualToResult (match &kb4 ((Label ax4) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $dv)
                      (((x y)) () () ()))

!(println! "")
!(println! "=== All add_a tests complete ===")
