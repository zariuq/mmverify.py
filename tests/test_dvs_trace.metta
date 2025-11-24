!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (DVar (c d) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))

!(println! "Manual trace through each DVar pair:")
!(println! "")

!(println! "Pair 1: (a b)")
!(let $x_found (matchc &self (kb1 (MandVar a)) found)
  (let $y_found (matchc &self (kb1 (MandVar b)) found)
    (progn
      (println! ("  x_found:" $x_found))
      (println! ("  y_found:" $y_found))
      (println! ("  not (== x_found ()):" (not (== $x_found ()))))
      (println! ("  not (== y_found ()):" (not (== $y_found ()))))
      (println! ("  and:" (and (not (== $x_found ())) (not (== $y_found ()))))))))

!(println! "")
!(println! "Pair 2: (c d)")
!(let $x_found (matchc &self (kb1 (MandVar c)) found)
  (let $y_found (matchc &self (kb1 (MandVar d)) found)
    (progn
      (println! ("  x_found:" $x_found))
      (println! ("  y_found:" $y_found))
      (println! ("  not (== x_found ()):" (not (== $x_found ()))))
      (println! ("  not (== y_found ()):" (not (== $y_found ()))))
      (println! ("  and:" (and (not (== $x_found ())) (not (== $y_found ()))))))))
