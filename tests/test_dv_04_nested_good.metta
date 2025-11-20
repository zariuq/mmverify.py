; Mathematical meaning:
;   Tests nested expressions with disjoint variable sets.
;   We have: (x = y) and (z = w) as two propositions.
;   The axiom requires the propositions to have NO variables in common.
;   First proposition uses variables {x, y}
;   Second proposition uses variables {z, w}
;   Since {x,y} ∩ {z,w} = ∅, this is valid!
;
;   Like: "I'm pairing 'Alice and Bob' with 'Carol and Dan' -
;   no person appears in both groups, so it's valid."
;
; Metamath equivalent (test_dv_04.mm):
;
; $c wff class = ( ) $.
; $v ph ps x y z w $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vx $f class x $.
; vy $f class y $.
; vz $f class z $.
; vw $f class w $.
;
; $d x y $. $d x z $. $d x w $.
; $d y z $. $d y w $. $d z w $.
;
; ax-eq $a wff ( x = y ) $.
;
; ${
;   $d ph ps $.
;   ax-pair $a wff ( ph ps ) $.
; $}
;
; test4_good $p wff ( ( x = y ) ( z = w ) ) $=
;   vx vy ax-eq vz vw ax-eq ax-pair
; $.
;
; Verification with metamath-knife:
;   0 diagnostics issued.
;
; PASSES - {x,y} and {z,w} are disjoint sets.

!(import! &self mmverify-utils)

!(println! "=== TEST 4: Nested Expressions Valid (PASS) ===")
!(println! "Complex expressions with disjoint variable sets\n")

!(bind! &stack (new-space))
!(bind! &kb (new-space))
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))

!(push-frame &fd)
!(add_c &kb "wff")
!(add_c &kb "class")
!(add_c &kb "=")
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_v &kb "z" 1)
!(add_v &kb "w" 1)
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_f &kb "vx" "class" "x" 1)
!(add_f &kb "vy" "class" "y" 1)
!(add_f &kb "vz" "class" "z" 1)
!(add_f &kb "vw" "class" "w" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)

; CRITICAL: Declare all pairs disjoint
!(add_d &kb ("x" "y" "z" "w") 1)

; Axiom: x = y (no DV)
!(add_a &kb "ax-eq" ("wff" "x" "=" "y"))

; Axiom: ph != ps
!(push-frame &fd)
!(add_d &kb ("ph" "ps") 2)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-pair(x=y, z=w)")
!(println! "First expr vars: {x,y}")
!(println! "Second expr vars: {z,w}")
!(println! "Declared: x,y,z,w all pairwise disjoint")
!(println! "Expected: SUCCESS\n")
!(add_p &kb &stack &sp "nested-good"
  ("wff" "(" "(" "x" "=" "y" ")" "(" "z" "=" "w" ")" ")")
  ("vx" "vy" "ax-eq" "vz" "vw" "ax-eq" "ax-pair") True)

!(println! "✓ Test completed successfully")

!(pop-frame &kb &fd)
