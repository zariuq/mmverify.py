!(import! &self ../mmverify-utils_petta)

!(println! "=== Debug add_mand_var ===")

; Add a variable to kb1
!(add-atom &self (kb1 (Var x (FSDepth 0) (Type "$v"))))
!(println! "Added Var x")

; Check if Var was added
!(println! ("Check Var:" (collapse (match &self (kb1 (Var x $_ (Type "$v"))) found))))

; Call add_mand_var - this should use &self with kb1 tag
!(println! ("Calling add_mand_var kb1 x"))
!(let $result (add_mand_var kb1 x)
  (println! ("Result:" $result)))

; Check if MandVar was added
!(println! ("Check MandVar:" (collapse (match &self (kb1 (MandVar x)) found))))
