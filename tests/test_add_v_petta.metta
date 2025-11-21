!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing add_v (Space version) - Full Suite ===")

!(println! "Test 1: Add var successfully")
!(bind! &kb1 (new-space))
!(add_v &kb1 "x" 0)
!(test (match &kb1 (Var "x" (FSDepth 0) (Type "$v")) found) found)

!(println! "Test 2: Error - duplicate var")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var "y" (FSDepth 0) (Type "$v")))
!(test (add_v &kb2 "y" 0) (Error (Var "y") "Var already declared and active."))

!(println! "Test 3: Error - constant collision")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Constant "z" (Type "$c")))
!(test (add_v &kb3 "z" 0) (Error (Constant "z") "Var already declared as constant."))

!(println! "Test 4: Multiple variables")
!(bind! &kb4 (new-space))
!(add_v &kb4 "x" 0)
!(add_v &kb4 "y" 0)
!(add_v &kb4 "z" 0)
; Check existence of all 3. collapse returns list. Order should be insertion order?
!(test (collapse (match &kb4 (Var $n (FSDepth 0) (Type "$v")) $n)) ("x" "y" "z"))

!(println! "Test 5: Different levels")
!(bind! &kb5 (new-space))
!(add_v &kb5 "x" 0)
!(add_v &kb5 "y" 1)
!(add_v &kb5 "z" 2)
!(test (match &kb5 (Var "x" (FSDepth $l) (Type "$v")) $l) 0)
!(test (match &kb5 (Var "y" (FSDepth $l) (Type "$v")) $l) 1)
!(test (match &kb5 (Var "z" (FSDepth $l) (Type "$v")) $l) 2)

!(println! "Test 6: Same name different levels (Should Error)")
!(bind! &kb6 (new-space))
!(add_v &kb6 "x" 0)
!(test (add_v &kb6 "x" 1) (Error (Var "x") "Var already declared and active."))
; Confirm only x at 0 exists
!(test (collapse (match &kb6 (Var "x" (FSDepth $l) (Type "$v")) $l)) (0))

!(println! "Test 7: Duplicate same level (Error)")
!(bind! &kb7 (new-space))
!(add_v &kb7 "x" 0)
!(test (add_v &kb7 "x" 0) (Error (Var "x") "Var already declared and active."))

!(println! "=== add_v tests complete ===")
