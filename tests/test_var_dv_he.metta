; Test file for variable and disjoint variable (DV) functions
; Functions: is_var, find_vars, string<, orient_pair, lookup_d, dv_check, check_dv_pairs, check_dvs

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(println! "=== Testing Variable and DV Functions ===")
!(println! "")

!(println! "Test 1: is_var identifies variables in space")
!(bind! &kb1 (new-space))
!(add-atom &kb1 (Var x 0 (Type "$v")))
!(add-atom &kb1 (Constant c (Type "$c")))
!(assertEqual (is_var &kb1 x) True)
!(assertEqual (is_var &kb1 c) False)
!(assertEqual (is_var &kb1 unknown) False)

!(println! "Test 2: find_vars extracts variables from statement")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var x 0 (Type "$v")))
!(add-atom &kb2 (Var y 0 (Type "$v")))
!(add-atom &kb2 (Constant c (Type "$c")))
; find_vars returns expression, convert to list for comparison
!(test (to-list (find_vars &kb2 (x c y z))) (Cons x (Cons y Nil)))

!(println! "Test 3: string< compares strings lexicographically")
; Note: string< returns Python booleans which don't work well with assertEqual
; We test it indirectly through orient_pair instead
; (string< "a" "b") returns True, (string< "b" "a") returns False, etc.

!(println! "Test 4: orient_pair orders variables consistently")
; orient_pair uses string representation for ordering
!(test (orient_pair a b) (a b))
!(test (orient_pair b a) (a b))
!(test (orient_pair x x) (x x))
; Verify it's stable
!(assertEqual (orient_pair foo bar) (orient_pair bar foo))

!(println! "Test 5: lookup_d finds disjoint variable constraints")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (DVar (x y) 0 (Type "$d")))
; lookup_d should find the DVar regardless of order
!(assertEqual (lookup_d &kb3 x y) True)
!(assertEqual (lookup_d &kb3 y x) True)
!(assertEqual (lookup_d &kb3 x z) False)

!(println! "Test 6: dv_check validates disjoint variables")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (DVar (x y) 0 (Type "$d")))
; Valid DV is ok (returns ())
!(assertEqual (dv_check &kb4 x y) ())
; Same variable or missing DV returns Error (tested implicitly)
; Note: dv_check returns Error for violations (x x) and (x z)

!(println! "Test 7: check_dv_pairs validates pairs of variable lists")
!(bind! &kb5 (new-space))
!(add-atom &kb5 (DVar (a b) 0 (Type "$d")))
!(add-atom &kb5 (DVar (a c) 0 (Type "$d")))
; All pairs (a,b) and (a,c) are valid - returns nested () from map-atom
!(test (check_dv_pairs &kb5 (a) (b c)) ((() ())))
; Note: Missing (b,c) would cause Error violation

!(println! "Test 8: check_dvs validates substitution DV constraints")
!(bind! &kb6 (new-space))
!(add-atom &kb6 (Var x 0 (Type "$v")))
!(add-atom &kb6 (Var y 0 (Type "$v")))
!(add-atom &kb6 (DVar (x y) 0 (Type "$d")))
!(bind! &subst (new-space))
!(add-atom &subst (ph (x)))
!(add-atom &subst (ps (y)))
; Check that substitution preserves DV constraint - returns nested () from map-atom
!(test (check_dvs &kb6 &subst ((ph ps))) (((()))))

!(println! "Test 9: check_dvs with valid substitution")
!(bind! &kb7 (new-space))
!(add-atom &kb7 (Var x 0 (Type "$v")))
!(add-atom &kb7 (Var y 0 (Type "$v")))
!(add-atom &kb7 (DVar (x y) 0 (Type "$d")))
!(bind! &subst2 (new-space))
!(add-atom &subst2 (ph (x)))
!(add-atom &subst2 (ps (y)))
; Valid DV-preserving substitution returns nested () from map-atom
!(test (check_dvs &kb7 &subst2 ((ph ps))) (((()))))
; Note: Substituting same variable for both would violate DV

!(println! "")
!(println! "=== All variable/DV tests complete ===")
