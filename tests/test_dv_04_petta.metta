; Test DV 04: Complex proof with 4 distinct vars, all have DVs
; Expected: Should succeed
!(import! &self ../mmverify-utils_petta)

!(println! "=== Test DV 04: Complex proof with 4 vars ===")

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
!(add_v &kb "w" 1)
!(add_f &kb "vph" "wff" "ph" 1)
!(add_f &kb "vps" "wff" "ps" 1)
!(add_f &kb "vx" "class" "x" 1)
!(add_f &kb "vy" "class" "y" 1)
!(add_f &kb "vz" "class" "z" 1)
!(add_f &kb "vw" "class" "w" 1)
; All pairs of x,y,z,w are disjoint
!(add_d &kb ("x" "y") 1)
!(add_d &kb ("x" "z") 1)
!(add_d &kb ("x" "w") 1)
!(add_d &kb ("y" "z") 1)
!(add_d &kb ("y" "w") 1)
!(add_d &kb ("z" "w") 1)
!(add_a &kb "ax-eq" ("wff" "(" "x" "=" "y" ")"))
!(add_d &kb ("ph" "ps") 1)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))

; Test: Valid proof with x,y for first eq and z,w for second
!(let $result (add_p &kb &stack &sp "test4_good" ("wff" "(" "(" "x" "=" "y" ")" "(" "z" "=" "w" ")" ")") ("vx" "vy" "ax-eq" "vz" "vw" "ax-eq" "ax-pair") True)
  (case $result
    (((Error $info $msg) (test False True))
     ($_ (test True True)))))
