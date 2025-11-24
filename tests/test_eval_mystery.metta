!(import! &self mmverify-utils_petta_partial)

!(println! "=== Exploring the eval mystery ===")

!(println! "")
!(println! "Test 1: Check what from-list returns in a function")
(= (test_from_list_bare $list)
  (let* (
      ($result (from-list $list))
    )
    ((Result $result))))

!(test_from_list_bare (Cons a (Cons b Nil)))

!(println! "")
!(println! "Test 2: Check what eval (from-list) returns in a function")
(= (test_from_list_eval $list)
  (let* (
      ($result (from-list $list))
    )
    ((Result (eval $result)))))

!(test_from_list_eval (Cons a (Cons b Nil)))

!(println! "")
!(println! "Test 3: Direct from-list in tuple return (like make_assertion)")
(= (test_direct_from_list $list)
  (let* (
      ($dummy 1)
    )
    ((Data (from-list $list)))))

!(test_direct_from_list (Cons x (Cons y Nil)))

!(println! "")
!(println! "Test 4: Direct eval (from-list) in tuple return")
(= (test_direct_eval_from_list $list)
  (let* (
      ($dummy 1)
    )
    ((Data (eval (from-list $list))))))

!(test_direct_eval_from_list (Cons x (Cons y Nil)))

!(println! "")
!(println! "Test 5: Can pattern match on unevaluated from-list result?")
(= (test_match_bare $list)
  (let $result ((FHyps (from-list $list)))
    (case $result
      (((FHyps ($first $rest:)) (println! ("Matched tuple:" $first $rest:)))
       ((FHyps $x) (println! ("Matched list:" $x)))
       ($other (println! ("No match:" $other)))))))

!(test_match_bare (Cons p (Cons q Nil)))

!(println! "")
!(println! "Test 6: Can pattern match on eval (from-list) result?")
(= (test_match_eval $list)
  (let $result ((FHyps (eval (from-list $list))))
    (case $result
      (((FHyps ($first $rest:)) (println! ("Matched tuple:" $first $rest:)))
       ((FHyps $x) (println! ("Matched list:" $x)))
       ($other (println! ("No match:" $other)))))))

!(test_match_eval (Cons p (Cons q Nil)))

!(println! "")
!(println! "Done!")
