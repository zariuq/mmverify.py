; MeTTa version of add_c - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &kb1 (new-space))
!(add_c &kb1 "0")
!(assertEqual (match &kb1 (Constant $name (Type "$c")) $name) "0")

; Test 2: Error case - try to add constant that already exists
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Constant "+" (Type "$c")))
!(assertEqual (add_c &kb2 "+") (Error (Constant "+") "Constant already declared."))

; Test 3: Error case - try to declare constant when variable with same name exists
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Var "x" 1 (Type "$v")))
!(assertEqual (add_c &kb3 "x") (Error (Var "x") "Trying to declare as a constant an active variable."))

; Test 4: Multiple constants should coexist
!(bind! &kb4 (new-space))
!(add_c &kb4 "0")
!(add_c &kb4 "+")
!(add_c &kb4 "=")
!(assertEqualToResult (match &kb4 (Constant $name (Type "$c")) $name) ("0" "+" "="))
