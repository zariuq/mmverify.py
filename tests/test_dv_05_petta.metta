; Test DV 05: Same var x appears in both parts of pair, violating DV
; Expected: Should fail with DV error
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 05: Same var x in both parts ===")

!(bind! &kb (new-space))
!(bind! &stack (new-space))
!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "class")
!(add_c &kb "=")
!(add_c &kb "(")
!(add_c &kb ")")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_v &kb "z" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vx" "class" "x" 1)
!(add_f &kb "vy" "class" "y" 1)
!(add_f &kb "vz" "class" "z" 1)
!(add_a &kb "ax-eq" ("wff" "(" "x" "=" "y" ")"))
!(add_d &kb ("ph" "ps") 1)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))

; Test: (vx vy ax-eq vx vz ax-eq ax-pair) - x appears in both eq's
; ax-pair requires ph != ps, but x is substituted for both
!(let $result (add_p &kb &stack &sp "test5_bad" ("wff" "(" "(" "x" "=" "y" ")" "(" "x" "=" "z" ")" ")") ("vx" "vy" "ax-eq" "vx" "vz" "ax-eq" "ax-pair") True)
  (case $result
    (((Error $info $_) (test True True))
     ($_ (test False True)))))
