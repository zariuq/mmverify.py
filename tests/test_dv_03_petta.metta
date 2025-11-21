; Test DV 03: Same var ps used twice with DV constraint
; Expected: Should fail with DV error
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 03: Same var ps twice with DV constraint ===")

!(bind! &kb (new-space))
!(bind! &stack (new-space))
!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "pair")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_d &kb ("ph" "ps") 1)
!(add_a &kb "ax-pair" ("wff" "pair" "ph" "ps"))

; Test: (vps vps ax-pair) - uses ps for both, violating DV
!(let $result (add_p &kb &stack &sp "test3_bad" ("wff" "pair" "ps" "ps") ("vps" "vps" "ax-pair") True)
  (case $result
    (((Error $info $_) (test True True))
     ($_ (test False True)))))
