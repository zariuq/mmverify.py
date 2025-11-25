; MeTTa version of add_c - Complete test suite (PeTTa version)
; Import all functions from mmverify-utils_petta.metta

!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing add_c (PeTTa version) ===")
!(println! "")

; Test 1: Add constant '0' successfully
!(println! "Test 1: Add constant '0' successfully")
!(println! "Calling add_c directly:")
!(add_c &kb1 "0")
!(test (match &kb1 (Constant $name (Type "$c")) $name) "0")

; Test 2: Error case - try to add constant that already exists
!(println! "Test 2: Error when adding duplicate constant")
!(add-atom &kb2 (Constant "+" (Type "$c")))
!(test (add_c &kb2 "+") (Error (Constant "+") "Constant already declared."))

; Test 3: Error case - try to declare constant when variable with same name exists
!(println! "Test 3: Error when declaring constant with active variable name")
!(add-atom &kb3 (Var "x" 1 (Type "$v")))
!(test (add_c &kb3 "x") (Error (Var "x") "Trying to declare as a constant an active variable."))

; Test 4: Multiple constants should coexist
!(println! "Test 4: Multiple constants coexist")
!(add_c &kb4 "0")
!(add_c &kb4 "+")
!(add_c &kb4 "=")
!(test (collapse (match &kb4 (Constant $name (Type "$c")) $name)) ("0" "+" "="))

!(println! "")
!(println! "=== All add_c tests complete ===")