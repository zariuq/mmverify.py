; PeTTa version of add_a test suite (new-space style)
!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing add_a (PeTTa) ===")
!(println! "")

!(println! "Test 1: Simple assertion with no hypotheses")
!(bind! &akb1 (new-space))
!(add_a &akb1 ax1 (wff P))
!(test (collapse (match &akb1 ((Label $l) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) ($l $s)))
       ((ax1 (wff P))))

!(println! "Test 2: Assertion with floating hypothesis (x appears in statement)")
!(bind! &akb2 (new-space))
!(add-atom &akb2 (Var x (FSDepth 0) (Type "$v")))
!(add-atom &akb2 (FList (FSDepth 1) (Cons (class x) Nil)))
; Statement includes x as a mandatory variable
!(add_a &akb2 ax2 (wff x))
!(test (collapse (match &akb2 ((Label ax2) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $fh))
       (((class x))))

!(println! "Test 3: Assertion with essential hypothesis")
!(bind! &akb3 (new-space))
!(add-atom &akb3 (EList (FSDepth 1) (Cons (wff P) Nil)))
!(add_a &akb3 ax3 (wff (implies P Q)))
!(test (collapse (match &akb3 ((Label ax3) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $eh))
       (((wff P))))

!(println! "Test 4: Assertion with disjoint variables (x, y in statement)")
!(bind! &akb4 (new-space))
!(add-atom &akb4 (Var x (FSDepth 0) (Type "$v")))
!(add-atom &akb4 (Var y (FSDepth 0) (Type "$v")))
!(add-atom &akb4 (DVar (x y) (FSDepth 1) (Type "$d")))
!(add-atom &akb4 (FList (FSDepth 1) (Cons (class x) (Cons (class y) Nil))))
; Statement must include x and y as tokens so they become mandatory vars
!(add_a &akb4 ax4 (wff x y))
; DVars result includes the pair
!(test (collapse (match &akb4 ((Label ax4) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a"))) $dv))
       (((x y))))

!(println! "")
!(println! "=== All add_a tests complete ===")
