!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (DVar (c d) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))
; c and d are NOT mandatory

!(println! "Test: Check if list is non-empty instead of == (found)")
!(let $result (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
                (let $x_found (matchc &self (kb1 (MandVar $x)) found)
                  (let $y_found (matchc &self (kb1 (MandVar $y)) found)
                    (if (and (not (== $x_found ())) (not (== $y_found ())))
                        ($x $y)
                        ()))))
  (println! ("Result:" $result)))

!(println! "Expected: ((a b)) - only the pair where both are mandatory")
