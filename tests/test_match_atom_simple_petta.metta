!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing match-atom (practical usage) ===")
!(println! "")

!(println! "Test 1: match-atom with collapse (actual usage pattern)")
!(test (collapse (match-atom (a b c a d) a a)) (a a))

!(println! "Test 2: match-atom' with collapse for levels (from make_assertion)")
; This is the pattern: ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
!(test (collapse (match-atom' ((1 x) (2 y) (1 z)) ($l $_) $l)) (1 2 1))

!(println! "Test 3: match-atom' in let binding (from treat_assertion)")
; This is the pattern: ($dvars (match-atom' $Data (DVars $dvars) $dvars))
!(let $Data ((DVars (x y)) (FHyps ()) (EHyps ()) (Statement (wff p)))
  (let $dvars (match-atom' $Data (DVars $dv) $dv)
    (test $dvars (x y))))

!(println! "Test 4: match-atom'' with Nil sentinel (from collect_lists_by_depth)")
; This is the pattern: (match-atom'' $unordered_list ($current $list) $list Nil)
!(test (match-atom'' ((1 (a b)) (2 (c d))) (1 $list) $list Nil)
       (a b))
!(test (match-atom'' ((2 (c d))) (1 $list) $list Nil)
       Nil)

!(println! "Test 5: Verify () handling with collapse")
; When nothing matches, match-atom' returns (), collapse gives (())
!(test (collapse (match-atom' (x y z) (a $val) $val)) (()))

!(println! "")
!(println! "=== All match-atom tests complete ✅ ===")
