!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing match-atom Functions ===")
!(println! "")

!(println! "Test 1: match-atom finds matching element in expression")
; match-atom is non-deterministic, returning each match
!(test (collapse (match-atom (a b c a d) a a)) (a a))
!(test (collapse (match-atom (1 2 3) 2 found)) (found))

!(println! "Test 2: match-atom with pattern extraction")
!(test (collapse (match-atom ((x 1) (y 2) (z 3)) ($name $val) $name)) (x y z))
!(test (collapse (match-atom ((x 1) (y 2) (z 3)) ($name $val) $val)) (1 2 3))

!(println! "Test 3: match-atom' returns (()) when no match (with collapse)")
; Note: collapse of () gives (()) - a list containing empty
; This is how it's used in make_assertion: (if (== $e_levels (())) ...)
!(test (collapse (match-atom' (a b c) d found)) (()))
!(test (collapse (match-atom' () x found)) (()))

!(println! "Test 4: match-atom' returns results when matches found")
; Single match - use collapse to get the value
!(test (collapse (match-atom' (foo bar baz) bar found)) (found))
; Multiple matches return separate results (non-deterministic)
!(test (collapse (match-atom' ((a 1) (b 2)) ($x $y) $x)) (a b))

!(println! "Test 5: match-atom'' with custom empty value")
!(test (match-atom'' (p q r) s found not-found) not-found)
!(test (match-atom'' (p q r) q found not-found) found)

!(println! "Test 6: collect_lists_by_depth with no data")
!(test (collect_lists_by_depth () 1 3 Nil) Nil)

!(println! "Test 7: collect_lists_by_depth with single level")
!(test (collect_lists_by_depth ((1 (Cons a Nil))) 1 1 Nil)
       (Cons a Nil))

!(println! "Test 8: collect_lists_by_depth with multiple levels")
; Note: match-atom'' is non-deterministic, so we collapse to get one result
!(let $result (collapse (collect_lists_by_depth ((1 (Cons a Nil)) (2 (Cons b Nil)) (1 (Cons c Nil))) 1 2 Nil))
  (println! ("Result:" $result)))

!(println! "")
!(println! "=== All match-atom tests complete ✅ ===")
