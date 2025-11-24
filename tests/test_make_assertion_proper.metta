!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing make_assertion with proper KB setup ===")

;; Setup a proper KB with variables and lists
!(add-atom &self (testkb (Var p (FSDepth 1) (Type "$v"))))
!(add-atom &self (testkb (Var x (FSDepth 1) (Type "$v"))))
!(add-atom &self (testkb (EList (FSDepth 1) (Cons (|- P) Nil))))
!(add-atom &self (testkb (FList (FSDepth 1) (Cons (wff p) (Cons (class x) Nil)))))

!(println! "Calling make_assertion...")
!(let $result (make_assertion testkb (wff (p -> x)))
  (println! ("Result:" $result)))

!(println! "Done!")
