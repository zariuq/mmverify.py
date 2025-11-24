!(import! &self mmverify-utils_petta_partial)

;; Test with first half of bindings only (before dvs)
(= (make_assertion $kb $stmt)
  (let*
    (
      ($e_hyps_lists (matchc &self ($kb (EList (FSDepth $level) $elist)) ($level $elist)))
      ($_1 (println! ("e_hyps lists:" $e_hyps_lists)))
      ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
      ($_2 (println! ("e_levels:" $e_levels)))
      ($e_max_level (if (== $e_levels (())) 0 (max-atom $e_levels)))
      ($_3 (println! ("max_level of ehyps frame stack:" $e_max_level)))
      ($e_hyps_list (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil))
      ($_4 (println! ("e_hyps_list:" $e_hyps_list)))
      ($e_hyps_toks (from-list (flatten-list $e_hyps_list)))
      ($_5 (map-atom $e_hyps_toks $tok (add_mand_var $kb $tok)))
      ($_6 (map-atom $stmt $tok (add_mand_var $kb $tok)))
      ($mand_vars (matchc &self ($kb (MandVar $var)) $var))
    ) (FirstHalf $e_hyps_list $mand_vars)))

!(println! "Testing first half...")
!(add-atom &self (testspace (EList (FSDepth 1) Nil)))
!(make_assertion testspace (wff p))
!(println! "Done!")
