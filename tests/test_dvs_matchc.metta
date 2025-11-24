!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing DV logic with matchc ===")

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (DVar (c d) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))
; c is NOT mandatory

!(println! "Test 1: Check what matchc returns for MandVar")
!(println! ("matchc a:" (matchc &self (kb1 (MandVar a)) found)))
!(println! ("matchc c:" (matchc &self (kb1 (MandVar c)) found)))

!(println! "")
!(println! "Test 2: Simple if-based filtering")
!(let $dvs (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
              (let $x_found (matchc &self (kb1 (MandVar $x)) found)
                (let $y_found (matchc &self (kb1 (MandVar $y)) found)
                  (if (and (not (== $x_found ())) (not (== $y_found ())))
                      ($x $y)
                      ()))))
  (println! ("DVs:" $dvs)))

!(println! "")
!(println! "Test 3: Using == to check for (found)")
!(let $dvs (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
              (if (and (== (matchc &self (kb1 (MandVar $x)) found) (found))
                       (== (matchc &self (kb1 (MandVar $y)) found) (found)))
                  ($x $y)
                  ()))
  (println! ("DVs with ==:" $dvs)))

!(println! "Done!")
