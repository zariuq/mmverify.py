; Simple test of apply_subst_tok alone

(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

!(bind! &s (new-space))

!(println! "Test 1: No substitution")
!(println! (apply_subst_tok &s x))

!(println! "\nTest 2: With substitution")
!(add-atom &s (t (term 0)))
!(println! (apply_subst_tok &s t))

!(println! "\nTest 3: Non-matching")
!(println! (apply_subst_tok &s r))

!(println! "\nTest 4: Multiple substitutions")
!(add-atom &s (r (term 5)))
!(println! (apply_subst_tok &s t))
!(println! (apply_subst_tok &s r))
