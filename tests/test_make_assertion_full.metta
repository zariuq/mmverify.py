!(import! &self mmverify-utils_petta_partial)

!(println! "===  Testing make_assertion from partial file ===")

;; Minimal KB setup
!(add-atom &self (testkb (EList (FSDepth 1) Nil)))
!(add-atom &self (testkb (FList (FSDepth 1) (Cons (wff p) Nil))))
!(add-atom &self (testkb (Var p (FSDepth 1) (Type "$v"))))

!(println! "Calling make_assertion...")
!(let $result (make_assertion testkb (wff p))
  (println! ("Result:" $result)))
!(println! "Done!")
