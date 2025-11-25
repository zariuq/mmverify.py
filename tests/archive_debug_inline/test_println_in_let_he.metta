; HE MeTTa Test: println! in let* expressions
; This demonstrates that println! WORKS in let* in HE MeTTa

!(println! "=== HE MeTTa: Testing println! in let* ===")
!(println! "")

!(println! "Test 1: println! with ! in let* with (() ...) pattern")
!(let*
  (
    ($a 1)
    (() (println! ("✅ HE: Inside let*, a =" $a)))
    ($b 2)
  )
  (+ $a $b))
!(println! "Test 1 complete")
!(println! "")

!(println! "Test 2: Multiple println! statements in let*")
!(let*
  (
    ($x 10)
    (() (println! ("✅ HE: x =" $x)))
    ($y 20)
    (() (println! ("✅ HE: y =" $y)))
    ($z (+ $x $y))
    (() (println! ("✅ HE: z = x + y =" $z)))
  )
  $z)
!(println! "Test 2 complete")
!(println! "")

!(println! "=== HE MeTTa tests complete ===")