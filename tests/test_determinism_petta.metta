;; test_determinism_petta.metta
;; Comprehensive non-determinism test for mmverify-utils_petta.metta
;; Tests that functions return SINGLE results, not multiple non-deterministic branches

!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)

;; Setup test environment
!(bind! &kb (new-space))
!(bind! &fd (new-state 1))
!(bind! &sp (new-state 0))
!(bind! &stack (new-space))

;; Add test data to KB
!(add-atom &kb (Var x (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var y (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var z (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var w (FSDepth 0) (Type "$v")))
!(add-atom &kb (Constant c (Type "$c")))
!(add-atom &kb (DVar (x y) (FSDepth 0) (Type "$d")))

!(println! "=== Testing mmverify-utils_petta.metta for non-determinism ===")
!(println! "")

;; Import the actual implementation
!(import! &self ../mmverify-utils_petta)

;; ============ find_vars tests ============
!(println! "--- find_vars ---")
!(test (collapse (find_vars &kb (x c y))) ((x y)))
!(test (collapse (find_vars &kb (x))) ((x)))
!(test (collapse (find_vars &kb (c))) (()))

;; ============ dv_check tests ============
!(println! "--- dv_check ---")
;; Same variable should error
;; NOTE: Can't use $_ twice in a pattern - PeTTa requires both to match same value!
;; Use distinct var names like $info $msg instead
!(let $r (collapse (dv_check &kb x x))
  (if (== (size-atom $r) 1)
      (case (car-atom $r)
        (((Error $info $msg) (println! "dv_check x x -> Error ✅"))
         ($other (println! "dv_check x x -> not Error ❌"))))
      (println! ("dv_check x x -> non-deterministic:" (size-atom $r) "results ❌"))))

;; Different variables: x and y ARE declared $d, so returns true
!(test (dv_check &kb x y) true)
;; x and z are NOT declared $d, so returns Error
!(let $r (collapse (dv_check &kb x z))
  (if (== (size-atom $r) 1)
      (case (car-atom $r)
        (((Error $info $msg) (println! "dv_check x z -> Error (correct - not declared) ✅"))
         ($other (println! "dv_check x z -> not Error ❌"))))
      (println! ("dv_check x z -> non-deterministic:" (size-atom $r) "results ❌"))))

;; ============ check_dv_pairs tests (CRITICAL - was non-deterministic) ============
!(println! "--- check_dv_pairs (CRITICAL) ---")

;; Setup substitution with multiple variables
!(bind! &subst_multi (new-space))
!(add-atom &subst_multi (x (a b)))   ;; x -> (a b), vars = {a, b}
!(add-atom &subst_multi (y (c d)))   ;; y -> (c d), vars = {c, d}
;; Add vars to KB
!(add-atom &kb (Var a (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var b (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var c (FSDepth 0) (Type "$v")))
!(add-atom &kb (Var d (FSDepth 0) (Type "$v")))
;; Add DVar declarations for a-c, a-d, b-c, b-d (all pairs between {a,b} and {c,d})
!(add-atom &kb (DVar (a c) (FSDepth 0) (Type "$d")))
!(add-atom &kb (DVar (a d) (FSDepth 0) (Type "$d")))
!(add-atom &kb (DVar (b c) (FSDepth 0) (Type "$d")))
!(add-atom &kb (DVar (b d) (FSDepth 0) (Type "$d")))

;; This creates 2x2=4 pairs to check. All declared $d, so should return true
!(let $r (collapse (check_dv_pairs &kb (a b) (c d)))
  (if (== (size-atom $r) 1)
      (case (car-atom $r)
        ((true (println! "check_dv_pairs (a b) (c d) -> true ✅"))
         ((Error $i $m) (println! ("check_dv_pairs (a b) (c d) -> Error ❌:" (Error $i $m))))
         ($other (println! ("check_dv_pairs (a b) (c d) -> unexpected:" $other "❌")))))
      (println! ("check_dv_pairs (a b) (c d) -> NON-DETERMINISTIC:" (size-atom $r) "results ❌"))))

;; Test with overlapping vars - b appears in both, should detect error
!(let $r (collapse (check_dv_pairs &kb (a b) (b c)))
  (if (== (size-atom $r) 1)
      (case (car-atom $r)
        (((Error $info $msg) (println! "check_dv_pairs (a b) (b c) -> Error (correct) ✅"))
         ($other (println! "check_dv_pairs (a b) (b c) -> no Error ❌"))))
      (println! ("check_dv_pairs overlap -> NON-DETERMINISTIC:" (size-atom $r) "results ❌"))))

;; ============ check_dvs tests ============
!(println! "--- check_dvs ---")

;; Empty DV list
!(test (collapse (check_dvs &kb &subst_multi ())) (true))

;; Valid DV - no overlap in substitutions
!(bind! &subst_valid (new-space))
!(add-atom &subst_valid (x (a)))
!(add-atom &subst_valid (y (c)))
!(let $r (collapse (check_dvs &kb &subst_valid ((x y))))
  (if (== (size-atom $r) 1)
      (println! ("check_dvs valid -> 1 result ✅:" (car-atom $r)))
      (println! ("check_dvs valid -> NON-DETERMINISTIC:" (size-atom $r) "results ❌"))))

;; Invalid DV - same var in both substitutions
!(bind! &subst_invalid (new-space))
!(add-atom &subst_invalid (x (a b)))
!(add-atom &subst_invalid (y (b c)))  ;; b appears in both!
!(let $r (collapse (check_dvs &kb &subst_invalid ((x y))))
  (if (== (size-atom $r) 1)
      (case (car-atom $r)
        (((Error $info $msg) (println! "check_dvs invalid -> Error ✅"))
         ($other (println! "check_dvs invalid -> no Error ❌"))))
      (println! ("check_dvs invalid -> NON-DETERMINISTIC:" (size-atom $r) "results ❌"))))

;; ============ lookup_d tests ============
!(println! "--- lookup_d ---")
!(test (lookup_d &kb x y) true)
!(test (lookup_d &kb x z) false)

!(println! "")
!(println! "=== Summary ===")
!(println! "All tests should show ✅")
!(println! "Any ❌ or 'NON-DETERMINISTIC' indicates a bug!")
