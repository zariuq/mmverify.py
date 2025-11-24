!(import! &self mmverify-utils_petta_partial)

;; Define a simple function with let* like make_assertion
(= (simple_func $arg)
  (let*
    (
      ($x (+ $arg 1))
      ($y (+ $x 1))
    )
    (Result $x $y)))

!(println! "Testing simple_func...")
!(simple_func 5)
!(println! "Done!")
