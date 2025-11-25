!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing add_d (Space version) - Full Suite ===")

!(println! "Test 1: Add pair")
!(add_d &kb1 ("x" "y") 0)
!(test (match &kb1 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b)) ("x" "y"))

!(println! "Test 2: Reverse order")
!(add_d &kb2 ("y" "x") 0)
!(test (match &kb2 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b)) ("x" "y"))

!(println! "Test 3: Three variables (3 pairs)")
!(add_d &kb3 ("x" "y" "z") 0)
; Expect (x y) (x z) (y z). Sorted.
!(test (collapse (match &kb3 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b))) (("x" "y") ("x" "z") ("y" "z")))

!(println! "Test 4: Idempotency")
!(add_d &kb4 ("x" "y") 0)
!(add_d &kb4 ("x" "y") 0)
!(add_d &kb4 ("y" "x") 0)
!(test (collapse (match &kb4 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b))) (("x" "y")))

!(println! "Test 5: Different levels")
!(add_d &kb5 ("x" "y") 0)
!(add_d &kb5 ("x" "y") 1)
!(test (collapse (match &kb5 (DVar ("x" "y") (FSDepth $l) (Type "$d")) $l)) (0 1))

!(println! "=== add_d tests complete ===")
