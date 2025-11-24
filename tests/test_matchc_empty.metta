!(import! &self mmverify-utils_petta_partial)

!(add-atom &self (kb1 (Item a)))
!(add-atom &self (kb1 (Item b)))
!(add-atom &self (kb1 (Item c)))

!(println! "Test: Does matchc collect () results?")
!(let $result (matchc &self (kb1 (Item $x))
                (if (== $x a)
                    (Found $x)
                    ()))
  (println! ("Result:" $result)))

!(println! "Expected: ((Found a)) or just (Found a)?")
!(println! "Actual shows if () is included in results")
