!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing Assignment Helper Functions ===")
!(println! "")

!(println! "Test 1: add_mand_var adds variable to MandVar set")
!(add_v &kb1 x 0)
; Adding a variable that exists adds MandVar entry (returns true from add-atom)
!(test (add_mand_var &kb1 x) true)
; Verify it was added
!(test (collapse (match &kb1 (MandVar $v) $v)) (x))

!(println! "Test 2: add_mand_var skips non-variables")
!(add_c &kb2 c)
; Adding a constant does nothing (no Var found, returns ())
!(test (add_mand_var &kb2 c) ())
; Verify nothing was added
!(test (collapse (match &kb2 (MandVar $v) $v)) ())

!(println! "Test 3: add_mand_var skips already-added variables")
!(add_v &kb3 x 0)
!(add-atom &kb3 (MandVar x))
; Adding again does nothing (already present, inner case returns ())
!(test (add_mand_var &kb3 x) ())
; Still only one entry
!(test (collapse (match &kb3 (MandVar $v) $v)) (x))

!(println! "")
!(println! "=== All assignment helper tests complete ✅ ===")
