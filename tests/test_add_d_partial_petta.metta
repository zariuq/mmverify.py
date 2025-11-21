!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing add_d with partial utils ===")

; Test 1: Add single pair
!(println! "Test 1: add_d kb1 (x y) 1")
!(add_d kb1 (x y) 1)
!(test (collapse (match &self (kb1 (DVar (x y) $_ (Type "$d"))) found))
       (found))

; Test 2: Multiple pairs from list
!(println! "Test 2: add_d kb2 (a b c) 2")
!(add_d kb2 (a b c) 2)
!(test (collapse (match &self (kb2 (DVar (a b) $_ (Type "$d"))) found))
       (found))
!(test (collapse (match &self (kb2 (DVar (a c) $_ (Type "$d"))) found))
       (found))
!(test (collapse (match &self (kb2 (DVar (b c) $_ (Type "$d"))) found))
       (found))

; Test 3: Duplicate should be ignored
!(println! "Test 3: add_d kb1 (x y) 1 again")
!(add_d kb1 (x y) 1)
; Should still have exactly one (x y) pair
!(test (collapse (match &self (kb1 (DVar (x y) $_ (Type "$d"))) found))
       (found))

; Test 4: Same variable twice should be ignored
!(println! "Test 4: add_d kb3 (z z) 3")
!(add_d kb3 (z z) 3)
!(test (collapse (match &self (kb3 (DVar $_ $_ (Type "$d"))) found))
       ())

!(println! "All tests completed")
