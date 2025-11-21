; MeTTa version of add_v - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &kb1 (new-space))
!(add_v &kb1 x 0)
!(assertEqual (match &kb1 (Var $name (FSDepth $level) (Type "$v")) ($name $level)) (x 0))

; Test 2: Error case - try to add variable that already exists
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var y 0 (Type "$v")))
!(assertEqual (add_v &kb2 y 0) (Error (Var y) "Var already declared and active."))

; Test 3: Error case - try to declare variable when constant with same name exists
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Constant z (Type "$c")))
!(assertEqual (add_v &kb3 z 0) (Error (Constant z) "Var already declared as constant."))

; Test 4: Multiple variables at same level should coexist
!(bind! &kb4 (new-space))
!(add_v &kb4 x 0)
!(add_v &kb4 y 0)
!(add_v &kb4 z 0)
!(assertEqualToResult (match &kb4 (Var $name (FSDepth 0) (Type "$v")) $name) (x y z))

; Test 5: Variables at different levels
!(bind! &kb5 (new-space))
!(add_v &kb5 x 0)
!(add_v &kb5 y 1)
!(add_v &kb5 z 2)
!(assertEqual (match &kb5 (Var x (FSDepth $l) (Type "$v")) $l) 0)
!(assertEqual (match &kb5 (Var y (FSDepth $l) (Type "$v")) $l) 1)
!(assertEqual (match &kb5 (Var z (FSDepth $l) (Type "$v")) $l) 2)

; Test 6: Same variable name at different levels (should both exist)
!(bind! &kb6 (new-space))
!(add_v &kb6 x 0)
!(add_v &kb6 x 1)
!(assertEqualToResult (match &kb6 (Var x (FSDepth $l) (Type "$v")) $l) (0 1))

; Test 7: Error - duplicate at same level
!(bind! &kb7 (new-space))
!(add_v &kb7 x 0)
!(assertEqual (add_v &kb7 x 0) (Error (Var x) "Var already declared and active."))
