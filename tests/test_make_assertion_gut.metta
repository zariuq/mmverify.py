!(import! &self mmverify-utils_petta_partial)

;; Override with minimal version
(= (make_assertion $kb $stmt)
  (let*
    (
      ($e_hyps_lists (matchc &self ($kb (EList (FSDepth $level) $elist)) ($level $elist)))
    )
    (Result $e_hyps_lists)))

!(println! "Testing minimal make_assertion...")
!(add-atom &self (testspace (EList (FSDepth 1) Nil)))
!(make_assertion testspace (wff p))
!(println! "Done!")
