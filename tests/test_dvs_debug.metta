!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))

!(println! "Test: Debug the if condition")
!(let $result (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
                (let $x_found (matchc &self (kb1 (MandVar $x)) found)
                  (let $y_found (matchc &self (kb1 (MandVar $y)) found)
                    (progn
                      (println! ("x:" $x "x_found:" $x_found))
                      (println! ("y:" $y "y_found:" $y_found))
                      (println! ("x_found == (found):" (== $x_found (found))))
                      (println! ("y_found == (found):" (== $y_found (found))))
                      (if (and (== $x_found (found)) (== $y_found (found)))
                          ($x $y)
                          ())))))
  (println! ("Final result:" $result)))
