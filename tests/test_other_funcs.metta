!(import! &self mmverify-utils_petta_partial)

!(println! "Testing other functions from partial file...")

!(println! "Test 1: matchc")
!(add-atom &self (test1 (Data x)))
!(test (matchc &self (test1 (Data $v)) $v) (x))

!(println! "Test 2: add_mand_var")
!(add-atom &self (test2 (Var y (FSDepth 0) (Type "$v"))))
!(test (add_mand_var test2 y) true)

!(println! "Test 3: is_var")
!(add-atom &self (test3 (Var z (FSDepth 0) (Type "$v"))))
!(test (is_var test3 z) true)

!(println! "Test 4: apply_subst_tok")
!(add-atom &self (sub1 (x (a b))))
!(test (apply_subst_tok sub1 x) (a b))
!(test (apply_subst_tok sub1 y) y)

!(println! "All tests passed!")
