!(import! &self mmverify-utils_petta_partial)

!(println! "=== Testing DV matching ===")

!(add-atom &self (kb1 (DVar (a b) (FSDepth 1) (Type "$d"))))
!(add-atom &self (kb1 (MandVar a)))
!(add-atom &self (kb1 (MandVar b)))

!(println! "Test 1: What does match return for MandVar?")
!(println! ("Match a:" (match &self (kb1 (MandVar a)) found)))
!(println! ("Match b:" (match &self (kb1 (MandVar b)) found)))

!(println! "")
!(println! "Test 2: What does collapse (match ...) return?")
!(println! ("Collapsed a:" (collapse (match &self (kb1 (MandVar a)) found))))
!(println! ("Collapsed b:" (collapse (match &self (kb1 (MandVar b)) found))))

!(println! "")
!(println! "Test 3: Testing case with collapsed match")
!(let $check_a (collapse (match &self (kb1 (MandVar a)) found))
  (case $check_a
    (((found) (println! "Pattern matched (found)"))
     (() (println! "Pattern matched ()"))
     ($other (println! ("No match, got:" $other))))))

!(println! "Done!")
