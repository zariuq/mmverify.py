!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing add_d with duplicate variables ===")

; Test 1: $d z z (same variable twice)
!(println! "Test 1: $d z z (same variable)")
!(add_d kb1 (z z) 1)
!(println! "  Result:")
!(println! (collapse (match &self (kb1 (DVar $pair $_ (Type "$d"))) $pair)))

; Test 2: $d x y z z (duplicate z in list)
!(println! "Test 2: $d x y z z (z appears twice)")
!(add_d kb2 (x y z z) 2)
!(println! "  Result:")
!(println! (collapse (match &self (kb2 (DVar $pair $_ (Type "$d"))) $pair)))

; Test 3: Verify we get exactly the pairs we expect from Test 2
!(println! "Test 3: Verify expected pairs from $d x y z z")
!(test (collapse (match &self (kb2 (DVar (x y) $_ (Type "$d"))) found)) (found))
!(test (collapse (match &self (kb2 (DVar (x z) $_ (Type "$d"))) found)) (found))
!(test (collapse (match &self (kb2 (DVar (y z) $_ (Type "$d"))) found)) (found))

; Count total pairs (should be 3, not 6 due to duplicates)
!(println! "Test 4: Count total pairs for kb2")
!(let $pairs (collapse (match &self (kb2 (DVar $p $_ (Type "$d"))) $p))
  (println! ("Total pairs:" $pairs)))

!(println! "All tests completed")
