!(import! &self mmverify-utils_petta_partial)

!(println! "=== Experiment 1: from-list in simple context ===")
!(let $list (Cons a (Cons b Nil))
  (println! ("from-list result:" (from-list $list))))

!(println! "")
!(println! "=== Experiment 2: from-list in let* return ===")
!(let* (
    ($list (Cons a (Cons b Nil)))
  )
  (println! ("from-list in return:" (from-list $list))))

!(println! "")
!(println! "=== Experiment 3: from-list in tuple return ===")
!(let* (
    ($list (Cons a (Cons b Nil)))
  )
  (println! ("Tuple with from-list:" (Result (from-list $list)))))

!(println! "")
!(println! "=== Experiment 4: from-list with eval in tuple return ===")
!(let* (
    ($list (Cons a (Cons b Nil)))
  )
  (println! ("Tuple with eval from-list:" (Result (eval (from-list $list))))))

!(println! "")
!(println! "=== Experiment 5: Testing if from-list returns unevaluated ===")
!(let $result (from-list (Cons x (Cons y Nil)))
  (println! ("Direct result:" $result)))

!(println! "")
!(println! "=== Experiment 6: from-list vs eval from-list ===")
!(let $list (Cons p (Cons q Nil))
  (let* (
      ($without_eval (from-list $list))
      ($with_eval (eval (from-list $list)))
    )
    (progn
      (println! ("Without eval:" $without_eval))
      (println! ("With eval:" $with_eval))
      (println! ("Are they equal?" (== $without_eval $with_eval))))))

!(println! "")
!(println! "=== Experiment 7: Complex nested structure (like make_assertion) ===")
!(let* (
    ($f_hyps (Cons (wff p) (Cons (class x) Nil)))
    ($e_hyps (Cons (|- P) Nil))
  )
  (println! ("Without eval:" ((FHyps (from-list $f_hyps)) (EHyps (from-list $e_hyps))))))

!(println! "")
!(println! "=== Experiment 8: Same with eval ===")
!(let* (
    ($f_hyps (Cons (wff p) (Cons (class x) Nil)))
    ($e_hyps (Cons (|- P) Nil))
  )
  (println! ("With eval:" ((FHyps (eval (from-list $f_hyps))) (EHyps (eval (from-list $e_hyps)))))))

!(println! "")
!(println! "=== Experiment 9: Can we match on unevaluated from-list? ===")
!(let $result ((Data (from-list (Cons a Nil))))
  (case $result
    (((Data (a)) (println! "Matched as (a)"))
     ((Data $x) (println! ("Matched as:" $x)))
     ($other (println! ("No match, got:" $other))))))

!(println! "")
!(println! "=== Experiment 10: Can we match on eval from-list? ===")
!(let $result ((Data (eval (from-list (Cons a Nil)))))
  (case $result
    (((Data (a)) (println! "Matched as (a)"))
     ((Data $x) (println! ("Matched as:" $x)))
     ($other (println! ("No match, got:" $other))))))

!(println! "")
!(println! "Done with experiments!")
