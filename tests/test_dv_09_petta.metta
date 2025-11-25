; Test DV 09: Four-way DV with x,y,x,z - should fail (x repeated)
; Expected: Should fail with DV error
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 09: Four-way DV with x repeated ===")

!(bind! &sp (new-state 0))

!(add_c &kb "wff")
!(add_c &kb "four")
!(add_c &kb "(")
!(add_c &kb ")")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "th" 1)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_v &kb "z" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vch" "wff" "ch" 1)
!(add_f &kb "vth" "wff" "th" 1)
!(add_f &kb "vx" "wff" "x" 1)
!(add_f &kb "vy" "wff" "y" 1)
!(add_f &kb "vz" "wff" "z" 1)
; All pairs of ph,ps,ch,th are disjoint
!(add_d &kb ("ph" "ps") 1)
!(add_d &kb ("ph" "ch") 1)
!(add_d &kb ("ph" "th") 1)
!(add_d &kb ("ps" "ch") 1)
!(add_d &kb ("ps" "th") 1)
!(add_d &kb ("ch" "th") 1)
!(add_a &kb "ax-4way" ("wff" "(" "ph" "ps" "ch" "th" ")"))

; Test: (vx vy vx vz ax-4way) - x appears in positions 1 and 3, violating DV
!(let $result (add_p &kb &stack &sp "test9_bad" ("wff" "(" "x" "y" "x" "z" ")") ("vx" "vy" "vx" "vz" "ax-4way") True)
  (case $result
    (((Error $info $_) (test True True))
     ($_ (test False True)))))
