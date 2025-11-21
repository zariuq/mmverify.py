; Test DV 01: Basic DV violation - same var used twice with DV constraint
; Expected: Should fail with DV error
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 01: Same var twice with DV constraint ===")

!(bind! &kb (new-space))
!(bind! &stack (new-space))
!(bind! &sp (new-state 0))
!(bind! &fd (new-state 0))

; Setup: constants and variables
!(add_c &kb "wff")
!(add_c &kb "pair")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)

; Add DV constraint between ph and ps
!(add_d &kb ("ph" "ps") 1)

; Add assertion with DV requirement
!(add_a &kb "ax-pair" ("wff" "pair" "ph" "ps"))

; Test: Try proof (vph vph ax-pair) - uses ph for both args, violating DV
!(let $result (add_p &kb &stack &sp "test1_bad" ("wff" "pair" "ph" "ph") ("vph" "vph" "ax-pair") True)
  (case $result
    (((Error $info $_) (test True True))  ; Expected: error
     ($_ (test False True)))))  ; Unexpected: no error
