; Test DV 07: Three-way DV with x,x,y - should fail (x repeated)
; Expected: Should fail with DV error
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 07: Three-way DV with x repeated ===")

!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "three")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vch" "wff" "ch" 1)
!(add_f &kb "vx" "wff" "x" 1)
!(add_f &kb "vy" "wff" "y" 1)
; DVs for assertion
!(add_d &kb ("ph" "ps") 1)
!(add_d &kb ("ph" "ch") 1)
!(add_d &kb ("ps" "ch") 1)
!(add_a &kb "ax-3way" ("wff" "three" "ph" "ps" "ch"))

; Test: (vx vx vy ax-3way) - x appears twice, violating DV
!(let $result (add_p &kb &stack &sp "test7_bad" ("wff" "three" "x" "x" "y") ("vx" "vx" "vy" "ax-3way") True)
  (case $result
    (((Error $info $_) (test True True))
     ($_ (test False True)))))
