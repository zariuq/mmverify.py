!(import! &self mmverify-utils_petta_partial)

;; Redefine make_assertion to test if it works
(= (make_assertion_test $kb $stmt)
  (let* (
      ($e_hyps_list Nil)
      ($f_hyps Nil)
    )
    ((DVars ()) (FHyps (eval (from-list $f_hyps))) (EHyps (eval (from-list $e_hyps_list))) (Statement $stmt))))

!(println! "Calling make_assertion_test...")
!(make_assertion_test testkb (wff p))

!(println! "")
!(println! "Calling make_assertion from partial file...")
!(make_assertion testkb (wff p))

!(println! "Done!")
