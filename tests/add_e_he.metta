; MeTTa version of add_e - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &kb1 (new-space))
!(add_e &kb1 e1 (wff (implies p q)) 0)
!(assertEqual (match &kb1 ((Label $l) EHyp (FSDepth $d) ((Statement $s) (Type "$e"))) ($l $s $d))
              (e1 (wff (implies p q)) 0))

; Test 2: Verify EList was created
!(assertEqual (match &kb1 (EList (FSDepth 0) $el) $el)
              (Cons (wff (implies p q)) Nil))

; Test 3: Add second essential hypothesis, verify EList updated
!(bind! &kb2 (new-space))
!(add_e &kb2 e1 (wff (implies p q)) 0)
!(add_e &kb2 e2 (wff p) 0)
!(assertEqual (match &kb2 (EList (FSDepth 0) $el) $el)
              (Cons (wff (implies p q)) (Cons (wff p) Nil)))

; Test 4: Multiple essential hypotheses at same level
!(bind! &kb3 (new-space))
!(add_e &kb3 e1 (wff (implies p q)) 0)
!(add_e &kb3 e2 (wff p) 0)
!(add_e &kb3 e3 (wff q) 0)
!(assertEqualToResult (match &kb3 ((Label $l) EHyp (FSDepth 0) ((Statement $s) (Type "$e"))) $l)
                      (e1 e2 e3))

; Test 5: Different levels create separate ELists
!(bind! &kb4 (new-space))
!(add_e &kb4 e1 (wff p) 0)
!(add_e &kb4 e2 (wff q) 1)
!(assertEqual (match &kb4 (EList (FSDepth 0) $el) $el)
              (Cons (wff p) Nil))
!(assertEqual (match &kb4 (EList (FSDepth 1) $el) $el)
              (Cons (wff q) Nil))

; Test 6: EList appends in order
!(bind! &kb5 (new-space))
!(add_e &kb5 e1 (wff p) 0)
!(add_e &kb5 e2 (wff q) 0)
!(add_e &kb5 e3 (wff r) 0)
!(assertEqual (match &kb5 (EList (FSDepth 0) $el) $el)
              (Cons (wff p) (Cons (wff q) (Cons (wff r) Nil))))
