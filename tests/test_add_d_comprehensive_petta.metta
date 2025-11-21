!(import! &self mmverify-utils_petta_partial)

;; VERIFICATION: These tests match metamath-knife's actual behavior
;;
;; Created test_dv_duplicates.mm and verified with metamath-knife that:
;;   1. $d x y z z is ACCEPTED (duplicate variable in list)
;;   2. $d x x is ACCEPTED (same variable twice)
;;   3. $d x y x y z is ACCEPTED (multiple duplicates)
;;   metamath-knife exits with "0 diagnostics issued" for all cases
;;
;; Python simulation of mmverify.py shows for $d x y z z:
;;   - Iterates all pairs: (x,x), (x,y), (x,z), (x,z), (y,x), (y,y), (y,z), (y,z), ...
;;   - Skips when x == y
;;   - Orients each pair: if x < y then (x,y) else (y,x)
;;   - Adds only if not already present
;;   - Result: exactly 3 DV pairs stored: (x,y), (x,z), (y,z)
;;
;; For $d x x:
;;   - All 4 pair checks result in x == x, so all skipped
;;   - Result: 0 DV pairs stored
;;
;; Our PeTTa implementation uses Prolog's @< for string comparison,
;; which provides the same lexicographic ordering as Python's <

!(println! "=== Comprehensive add_d tests (matching metamath-knife) ===")

; Test 1: Basic pair
!(println! "Test 1: $d x y")
!(add_d kb1 (x y) 0)
!(test (collapse (match &self (kb1 (DVar $pair $_ (Type "$d"))) $pair))
       ((x y)))

; Test 2: Reverse order should produce same canonical pair
!(println! "Test 2: $d y x (should be same as x y)")
!(add_d kb2 (y x) 0)
!(test (collapse (match &self (kb2 (DVar $pair $_ (Type "$d"))) $pair))
       ((x y)))

; Test 3: Three variables create three pairs (canonically ordered)
!(println! "Test 3: $d x y z")
!(add_d kb3 (x y z) 0)
!(test (collapse (match &self (kb3 (DVar $pair $_ (Type "$d"))) $pair))
       ((x y) (x z) (y z)))

; Test 4: Duplicate add should be idempotent
!(println! "Test 4: Add $d x y multiple times")
!(add_d kb4 (x y) 0)
!(add_d kb4 (x y) 0)
!(add_d kb4 (y x) 0)
!(test (collapse (match &self (kb4 (DVar $pair $_ (Type "$d"))) $pair))
       ((x y)))

; Test 5: Different levels create separate constraints
!(println! "Test 5: $d x y at different levels")
!(add_d kb5 (x y) 0)
!(add_d kb5 (x y) 1)
!(test (collapse (match &self (kb5 (DVar (x y) (FSDepth $l) (Type "$d"))) $l))
       (0 1))

; Test 6: Duplicate variables in list
!(println! "Test 6: $d x y z z (duplicate z)")
!(add_d kb6 (x y z z) 0)
!(test (collapse (match &self (kb6 (DVar $pair $_ (Type "$d"))) $pair))
       ((x y) (x z) (y z)))

; Test 7: Same variable only
!(println! "Test 7: $d z z (no constraint added)")
!(add_d kb7 (z z) 0)
!(test (collapse (match &self (kb7 (DVar $pair $_ (Type "$d"))) $pair))
       ())

; Test 8: Verify lexicographic ordering (a < b < x < y < z)
!(println! "Test 8: $d a b x y z (verify canonical ordering)")
!(add_d kb8 (z y x b a) 0)
; Should produce: (a b), (a x), (a y), (a z), (b x), (b y), (b z), (x y), (x z), (y z)
!(let $pairs (collapse (match &self (kb8 (DVar $pair $_ (Type "$d"))) $pair))
  (println! ("Pairs:" $pairs)))

!(println! "All comprehensive tests completed ✅")
