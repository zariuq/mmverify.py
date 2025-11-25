!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing add_f (Space version) - Full Suite ===")

; Test 1: Add floating hypothesis successfully
!(println! "Test 1: Add FHyp successfully")
!(add-atom &kb1 (Constant "class" (Type "$c")))
!(add-atom &kb1 (Var "x" (FSDepth 0) (Type "$v")))
!(add_f &kb1 "vx" "class" "x" 0)
!(test (collapse (match &kb1 ((Label $l) FHyp (FSDepth $d) ((Typecode $tc) (FVar $v) (Type "$f"))) ($l $tc $v $d)))
       (("vx" "class" "x" 0)))

; Test 2: Verify FList was created
!(println! "Test 2: Verify FList created")
!(test (collapse (match &kb1 (FList (FSDepth 0) $fl) $fl))
       ((Cons ("class" "x") Nil)))

; Test 3: Add second floating hypothesis, verify FList updated
!(println! "Test 3: Second FHyp updates FList")
!(add-atom &kb2 (Constant "class" (Type "$c")))
!(add-atom &kb2 (Constant "wff" (Type "$c")))
!(add-atom &kb2 (Var "x" (FSDepth 0) (Type "$v")))
!(add-atom &kb2 (Var "y" (FSDepth 0) (Type "$v")))
!(add_f &kb2 "vx" "class" "x" 0)
!(add_f &kb2 "vy" "wff" "y" 0)
!(test (collapse (match &kb2 (FList (FSDepth 0) $fl) $fl))
       ((Cons ("class" "x") (Cons ("wff" "y") Nil))))

; Test 4: Error - variable not declared
!(println! "Test 4: Error - var not declared")
!(add-atom &kb3 (Constant "class" (Type "$c")))
!(test (add_f &kb3 "vx" "class" "z" 0)
       (Error (Var "z") "Var in $f not declared."))

; Test 5: Error - typecode not declared
!(println! "Test 5: Error - typecode not declared")
!(add-atom &kb4 (Var "x" (FSDepth 0) (Type "$v")))
!(test (add_f &kb4 "vx" "foo" "x" 0)
       (Error (Constant "foo") "Typecode in $f not declared."))

; Test 6: Error - variable already typed
!(println! "Test 6: Error - var already typed")
!(add-atom &kb5 (Constant "class" (Type "$c")))
!(add-atom &kb5 (Var "x" (FSDepth 0) (Type "$v")))
!(add_f &kb5 "vx" "class" "x" 0)
!(test (add_f &kb5 "vx2" "class" "x" 0)
       (Error ((Label "vx") (Typecode "class") (Var "x")) "Var in $f already typed by an active $f-statement."))

; Test 7: Different levels create separate FLists
!(println! "Test 7: Different levels = separate FLists")
!(add-atom &kb6 (Constant "class" (Type "$c")))
!(add-atom &kb6 (Var "x" (FSDepth 0) (Type "$v")))
!(add-atom &kb6 (Var "y" (FSDepth 0) (Type "$v")))
!(add_f &kb6 "vx" "class" "x" 0)
!(add_f &kb6 "vy" "class" "y" 1)
!(test (collapse (match &kb6 (FList (FSDepth 0) $fl) $fl))
       ((Cons ("class" "x") Nil)))
!(test (collapse (match &kb6 (FList (FSDepth 1) $fl) $fl))
       ((Cons ("class" "y") Nil)))

!(println! "=== add_f tests complete ===")
