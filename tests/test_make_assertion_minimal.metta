!(import! &self mmverify-utils_petta_partial)

!(println! "=== Minimal make_assertion test ===")

;; Set up minimal kb data
!(add-atom &self (testkb (Constant term (Type "$c"))))
!(add-atom &self (testkb (Var t (FSDepth 1) (Type "$v"))))
!(add-atom &self (testkb (EList (FSDepth 1) Nil)))
!(add-atom &self (testkb (FList (FSDepth 1) (Cons (term t) Nil))))

!(println! "KB setup complete, calling make_assertion...")
!(let $result (make_assertion testkb (term t))
  (println! ("Result:" $result)))

!(println! "Done!")
