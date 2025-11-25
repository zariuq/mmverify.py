; Test DV 06: Three-way DV with 3 distinct vars
; Expected: Should succeed
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 06: Three-way DV with 3 distinct vars ===")

!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "three")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "th" 1)
!(add_v &kb "ta" 1)
!(add_v &kb "et" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vch" "wff" "ch" 1)
!(add_f &kb "vth" "wff" "th" 1)
!(add_f &kb "vta" "wff" "ta" 1)
!(add_f &kb "vet" "wff" "et" 1)
; DVs for th, ta, et
!(add_d &kb ("th" "ta") 1)
!(add_d &kb ("th" "et") 1)
!(add_d &kb ("ta" "et") 1)
; DVs for assertion
!(add_d &kb ("ph" "ps") 1)
!(add_d &kb ("ph" "ch") 1)
!(add_d &kb ("ps" "ch") 1)
!(add_a &kb "ax-3way" ("wff" "three" "ph" "ps" "ch"))

; Test: Valid proof with th, ta, et (all different, all have DVs)
!(let $result (add_p &kb &stack &sp "test6_good" ("wff" "three" "th" "ta" "et") ("vth" "vta" "vet" "ax-3way") True)
  (case $result
    (((Error $info $msg) (test False True))
     ($_ (test True True)))))
