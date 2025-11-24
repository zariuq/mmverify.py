!(import! &self ../mmverify-utils_petta)

!(println! "=== Compare new-space vs tagged atom ===")

; Test 1: Using new-space (like add_c, add_v, etc. do)
!(bind! &kb1 (new-space))
!(add_v &kb1 x 0)
!(println! ("new-space check Var:" (collapse (match &kb1 (Var x $_ (Type "$v")) found))))

; Try add_mand_var with new-space
!(println! ("Calling add_mand_var &kb1 x"))
!(let $result (add_mand_var &kb1 x)
  (println! ("Result:" $result)))
!(println! ("new-space check MandVar:" (collapse (match &kb1 (MandVar x) found))))

!(println! "")

; Test 2: Tagged atoms in &self (what the test is trying to do)
!(add-atom &self (kb2 (Var y (FSDepth 0) (Type "$v"))))
!(println! ("tagged check Var:" (collapse (match &self (kb2 (Var y $_ (Type "$v"))) found))))

; Try add_mand_var with tag
!(println! ("Calling add_mand_var kb2 y"))
!(let $result (add_mand_var kb2 y)
  (println! ("Result:" $result)))
!(println! ("tagged check MandVar:" (collapse (match &self (kb2 (MandVar y)) found))))
