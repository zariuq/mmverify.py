; Test DV 08: No DV constraint required, simple proof
; Expected: Should succeed
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 08: No DV constraint required ===")

!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "nocnstr")
!(add_v &kb "ph" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_a &kb "ax-no-dv" ("wff" "nocnstr" "ph"))

; Test: Simple proof with no DV requirements
!(let $result (add_p &kb &stack &sp "test8_good" ("wff" "nocnstr" "ph") ("vph" "ax-no-dv") True)
  (case $result
    (((Error $info $msg) (test False True))
     ($_ (test True True)))))
