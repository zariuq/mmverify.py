!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing Helper Functions ===")
!(println! "")
!(println! "Note: to-list, from-list, mappend, flatten-list tested in test_list_ops_petta.metta")
!(println! "")

!(println! "Test 1: max-atom finds maximum")
!(test (max-atom (1 3 2 5 4)) 5)

!(println! "Test 2: collect_lists_by_depth - empty case")
!(test (collect_lists_by_depth () 1 0 Nil) Nil)

!(println! "Test 3: collect_lists_by_depth - single level (with collapse)")
; In actual usage: ($e_hyps_list (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil))
; The result is non-deterministic but we use it directly in let binding
!(test (collapse (collect_lists_by_depth ((1 (Cons a Nil))) 1 1 Nil))
       ((Cons a Nil)))

!(println! "Test 4: collect_lists_by_depth - multiple levels")
; Collects lists from depth 1 to max_level in order, concatenating them with mappend
; In real usage, each depth has exactly one list, so this is deterministic
; This test uses multiple lists at depth 1 to verify the collection behavior
!(test (collapse (collect_lists_by_depth ((1 (Cons a Nil)) (2 (Cons b Nil)) (1 (Cons c Nil))) 1 2 Nil))
       ((Cons a (Cons b Nil)) (Cons c (Cons b Nil))))

!(println! "Test 5: add_mand_var adds mandatory variables")
!(add-atom &hkb1 (Var x (FSDepth 0) (Type "$v")))
!(add_mand_var &hkb1 x)
!(test (collapse (match &hkb1 (MandVar $v) $v)) (x))

!(println! "Test 6: assign_f_hyps filters by mandatory vars")
!(add-atom &hkb2 (Var x (FSDepth 0) (Type "$v")))
!(add-atom &hkb2 (Var y (FSDepth 0) (Type "$v")))
!(add-atom &hkb2 (MandVar x))
!(add-atom &hkb2 (MandVar y))
!(test (assign_f_hyps &hkb2 (Cons (class x) (Cons (wff y) (Cons (class z) Nil))))
       (Cons (class x) (Cons (wff y) Nil)))

!(println! "")
!(println! "=== All helper tests complete ✅ ===")
