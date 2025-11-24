!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (DVar (c d) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))

!(println! "Test: Use case instead of if to avoid generating ()")
!(let $result (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
                (case (matchc &self (kb1 (MandVar $x)) found)
                  ((() ())  ; If x not found, return ()
                   ($x_result   ; If x found, check y
                     (case (matchc &self (kb1 (MandVar $y)) found)
                       ((() ())  ; If y not found, return ()
                        ($y_result ($x $y))))))))  ; If y found, return pair
  (println! ("Result:" $result)))
