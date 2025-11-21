; Test DV 02: Valid proof - different vars with DV declared
; Expected: Should succeed
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 02: Different vars with DV declared ===")

!(bind! &kb (new-space))
!(bind! &stack (new-space))
!(bind! &sp (new-state 0))

; Setup: constants and variables
!(add_c &kb "wff")
!(add_c &kb "pair")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "th" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vch" "wff" "ch" 1)
!(add_f &kb "vth" "wff" "th" 1)

; Add DV constraint between ch and th
!(add_d &kb ("ch" "th") 1)

; Add DV constraint between ph and ps for the assertion
!(add_d &kb ("ph" "ps") 1)

; Add assertion with DV requirement (ph != ps)
!(add_a &kb "ax-pair" ("wff" "pair" "ph" "ps"))

; Test: Proof (vch vth ax-pair) - ch and th are different and have DV declared
!(let $result (add_p &kb &stack &sp "test2_good" ("wff" "pair" "ch" "th") ("vch" "vth" "ax-pair") True)
  (case $result
    (((Error $info $msg) (test False True))  ; Unexpected: error
     ($_ (test True True)))))  ; Expected: success (no error)
