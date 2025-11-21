; MeTTa version of add_f - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &kb1 (new-space))
!(add-atom &kb1 (Constant class (Type "$c")))
!(add-atom &kb1 (Var x 0 (Type "$v")))
!(add_f &kb1 vx class x 0)
!(assertEqual (match &kb1 ((Label $l) FHyp (FSDepth $d) ((Typecode $tc) (FVar $v) (Type "$f"))) ($l $tc $v $d))
              (vx class x 0))

; Test 2: Verify FList was created
!(assertEqual (match &kb1 (FList (FSDepth 0) $fl) $fl)
              (Cons (class x) Nil))

; Test 3: Add second floating hypothesis, verify FList updated
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Constant class (Type "$c")))
!(add-atom &kb2 (Constant wff (Type "$c")))
!(add-atom &kb2 (Var x 0 (Type "$v")))
!(add-atom &kb2 (Var y 0 (Type "$v")))
!(add_f &kb2 vx class x 0)
!(add_f &kb2 vy wff y 0)
!(assertEqual (match &kb2 (FList (FSDepth 0) $fl) $fl)
              (Cons (class x) (Cons (wff y) Nil)))

; Test 4: Error - variable not declared
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Constant class (Type "$c")))
!(assertEqual (add_f &kb3 vx class z 0)
              (Error (Var z) "Var in $f not declared."))

; Test 5: Error - typecode not declared
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var x 0 (Type "$v")))
!(assertEqual (add_f &kb4 vx foo x 0)
              (Error (Constant foo) "Typecode in $f not declared."))

; Test 6: Error - variable already typed
!(bind! &kb5 (new-space))
!(add-atom &kb5 (Constant class (Type "$c")))
!(add-atom &kb5 (Var x 0 (Type "$v")))
!(add_f &kb5 vx class x 0)
!(assertEqual (add_f &kb5 vx2 class x 0)
              (Error ((Label vx) (Typecode class) (Var x)) "Var in $f already typed by an active $f-statement."))

; Test 7: Different levels create separate FLists
!(bind! &kb6 (new-space))
!(add-atom &kb6 (Constant class (Type "$c")))
!(add-atom &kb6 (Var x 0 (Type "$v")))
!(add-atom &kb6 (Var y 0 (Type "$v")))
!(add_f &kb6 vx class x 0)
!(add_f &kb6 vy class y 1)
!(assertEqual (match &kb6 (FList (FSDepth 0) $fl) $fl)
              (Cons (class x) Nil))
!(assertEqual (match &kb6 (FList (FSDepth 1) $fl) $fl)
              (Cons (class y) Nil))
