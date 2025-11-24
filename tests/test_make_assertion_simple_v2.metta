!(import! &self mmverify-utils_petta_partial)

;; Test with explicit debug output
!(println! "=== Test make_assertion evaluation ===")

;; Setup
!(add-atom &self (testspace (EList (FSDepth 1) Nil)))
!(add-atom &self (testspace (FList (FSDepth 1) Nil)))

;; Try calling
!(println! "About to call make_assertion...")
!(make_assertion testspace (wff p))
!(println! "After calling make_assertion")

!(println! "Done!")
