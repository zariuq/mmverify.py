!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing eval in function definitions ===")

!(println! "")
!(println! "--- Test 1: Function WITHOUT eval in return ---")
(= (test_func_no_eval $list)
  (let* (
      ($result (from-list $list))
    )
    ((FHyps $result))))

!(println! "Calling test_func_no_eval...")
!(test_func_no_eval (Cons a (Cons b Nil)))

!(println! "")
!(println! "--- Test 2: Function WITH eval in return ---")
(= (test_func_with_eval $list)
  (let* (
      ($result (from-list $list))
    )
    ((FHyps (eval $result)))))

!(println! "Calling test_func_with_eval...")
!(test_func_with_eval (Cons a (Cons b Nil)))

!(println! "")
!(println! "--- Test 3: Function WITHOUT eval, from-list in return directly ---")
(= (test_func_direct_no_eval $list)
  (let* (
      ($dummy 1)
    )
    ((FHyps (from-list $list)))))

!(println! "Calling test_func_direct_no_eval...")
!(test_func_direct_no_eval (Cons a (Cons b Nil)))

!(println! "")
!(println! "--- Test 4: Function WITH eval, from-list in return directly ---")
(= (test_func_direct_with_eval $list)
  (let* (
      ($dummy 1)
    )
    ((FHyps (eval (from-list $list))))))

!(println! "Calling test_func_direct_with_eval...")
!(test_func_direct_with_eval (Cons a (Cons b Nil)))

!(println! "")
!(println! "--- Test 5: Check if function definitions exist ---")
!(match &self (= (test_func_no_eval $x) $body) (println! "test_func_no_eval exists"))
!(match &self (= (test_func_with_eval $x) $body) (println! "test_func_with_eval exists"))
!(match &self (= (test_func_direct_no_eval $x) $body) (println! "test_func_direct_no_eval exists"))
!(match &self (= (test_func_direct_with_eval $x) $body) (println! "test_func_direct_with_eval exists"))

!(println! "")
!(println! "--- Test 6: Complex function mimicking make_assertion structure ---")
(= (mini_make_assertion_no_eval $kb)
  (let* (
      ($f_hyps_list (Cons (wff p) Nil))
      ($e_hyps_list (Cons (|- P) Nil))
    )
    ((FHyps (from-list $f_hyps_list)) (EHyps (from-list $e_hyps_list)))))

!(println! "Calling mini_make_assertion_no_eval...")
!(mini_make_assertion_no_eval testkb)

!(println! "")
!(println! "--- Test 7: Same with eval ---")
(= (mini_make_assertion_with_eval $kb)
  (let* (
      ($f_hyps_list (Cons (wff p) Nil))
      ($e_hyps_list (Cons (|- P) Nil))
    )
    ((FHyps (eval (from-list $f_hyps_list))) (EHyps (eval (from-list $e_hyps_list))))))

!(println! "Calling mini_make_assertion_with_eval...")
!(mini_make_assertion_with_eval testkb)

!(println! "")
!(println! "Done!")
