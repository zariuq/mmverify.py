!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (MandVar a)))

!(println! "Test: What does matchc return when nothing matches?")
!(let $found (matchc &self (kb1 (MandVar a)) result)
  (println! ("Found a:" $found)))

!(let $not_found (matchc &self (kb1 (MandVar nothere)) result)
  (println! ("Not found:" $not_found)))

!(println! "")
!(println! "Test: Equality checks")
!(println! ("() == ():" (== () ())))
!(println! ("not (== () ()):" (not (== () ()))))

!(let $empty ()
  (progn
    (println! ("$empty:" $empty))
    (println! ("$empty == ():" (== $empty ())))
    (println! ("not (== $empty ()):" (not (== $empty ()))))))
