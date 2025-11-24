!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (DVar (c d) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))

;; Define a filter function to remove () elements
(= (filter-empty $list)
  (case $list
    ((Nil Nil)
     ((Cons $head $tail)
      (if (== $head ())
          (filter-empty $tail)
          (Cons $head (filter-empty $tail)))))))

!(println! "Test: Filter out () results after matchc")
!(let $raw (matchc &self (kb1 (DVar ($x $y) $_ (Type "$d")))
              (if (and (not (== (matchc &self (kb1 (MandVar $x)) found) ()))
                       (not (== (matchc &self (kb1 (MandVar $y)) found) ())))
                  ($x $y)
                  ()))
  (progn
    (println! ("Raw result:" $raw))
    (let $filtered (filter-empty (from-list $raw))
      (println! ("Filtered:" (from-list $filtered))))))
