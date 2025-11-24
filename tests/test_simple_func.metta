!(import! &self mmverify-utils_petta_partial)

;; Define a simple test function
(= (test_func $x) (Wrapped $x))

!(println! "Testing simple function...")
!(test_func hello)
!(println! "Done!")
