!(import! &self mmverify-utils_petta_partial)

!(println! "Checking if make_assertion is defined...")
!(match &self (= (make_assertion $kb $stmt) $body)
  (println! "Found definition!"))
!(println! "Done checking")
