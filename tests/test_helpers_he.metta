; MeTTa version of helper functions - test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; ===== Tests =====

!(println! "=== Testing Helper Functions ===")
!(println! "")

!(println! "Test 1: to-list converts expression to Cons/Nil")
!(assertEqual (to-list (a b c)) (Cons a (Cons b (Cons c Nil))))

!(println! "Test 2: from-list converts Cons/Nil to expression")
!(assertEqual (from-list (Cons a (Cons b (Cons c Nil)))) (a b c))

!(println! "Test 3: mappend concatenates lists")
!(assertEqual (mappend (Cons a (Cons b Nil)) (Cons c (Cons d Nil)))
              (Cons a (Cons b (Cons c (Cons d Nil)))))

!(println! "Test 4: flatten-list flattens nested expression lists")
!(assertEqual (flatten-list (Cons (a b) (Cons c Nil)))
              (Cons a (Cons b (Cons c Nil))))

!(println! "Test 5: max-atom finds maximum")
!(assertEqual (max-atom (1 3 2 5 4)) 5.0)

!(println! "Test 6: collect_lists_by_depth - empty case")
!(assertEqual (collect_lists_by_depth () 1 0 Nil) Nil)

!(println! "Test 7: collect_lists_by_depth - single level")
!(assertEqual (collect_lists_by_depth ((1 (Cons a Nil))) 1 1 Nil)
              (Cons a Nil))

!(println! "Test 8: collect_lists_by_depth - multiple levels (non-deterministic)")
; collect_lists_by_depth returns multiple results due to match-atom'' non-determinism
; This is expected behavior - in actual use it's within let* context
!(assertEqualToResult (collect_lists_by_depth ((1 (Cons a Nil)) (2 (Cons b Nil)) (1 (Cons c Nil))) 1 2 Nil)
                      ((Cons a (Cons b Nil)) (Cons c (Cons b Nil))))

!(println! "Test 9: add_mand_var adds mandatory variables")
!(bind! &kb1 (new-space))
!(add-atom &kb1 (Var x 0 (Type "$v")))
!(add_mand_var &kb1 x)
!(assertEqual (match &kb1 (MandVar $v) $v) x)

!(println! "Test 10: assign_f_hyps filters by mandatory vars")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var x 0 (Type "$v")))
!(add-atom &kb2 (Var y 0 (Type "$v")))
!(add-atom &kb2 (MandVar x))
!(add-atom &kb2 (MandVar y))
!(assertEqual (assign_f_hyps &kb2 (Cons (class x) (Cons (wff y) (Cons (class z) Nil))))
              (Cons (class x) (Cons (wff y) Nil)))

!(println! "")
!(println! "=== All helper tests complete ===")
