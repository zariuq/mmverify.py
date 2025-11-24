!(import! &self mmverify-utils_petta_partial)

;; Override with more complete version - add just one more binding
(= (make_assertion $kb $stmt)
  (let*
    (
      ($e_hyps_lists (matchc &self ($kb (EList (FSDepth $level) $elist)) ($level $elist)))
      ($_1 (println! ("e_hyps lists:" $e_hyps_lists)))
      ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
    )
    (Result $e_hyps_lists $e_levels)))

!(println! "Testing make_assertion with 3 bindings...")
!(add-atom &self (testspace (EList (FSDepth 1) Nil)))
!(make_assertion testspace (wff p))
!(println! "Done!")
