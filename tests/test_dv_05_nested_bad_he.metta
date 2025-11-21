; Mathematical meaning:
;   Tests nested expressions with OVERLAPPING variable sets.
;   We have: (x = y) and (x = z) as two propositions.
;   The axiom requires NO common variables between propositions.
;   First proposition uses variables {x, y}
;   Second proposition uses variables {x, z}
;   Since {x,y} ∩ {x,z} = {x} ≠ ∅, this VIOLATES the constraint!
;
;   Like: "I'm trying to pair 'Alice and Bob' with 'Alice and Carol' -
;   but Alice appears in BOTH groups, so it's invalid!"
;
; Metamath equivalent (test_dv_05.mm):
;
; $c wff class = ( ) $.
; $v ph ps x y z $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vx $f class x $.
; vy $f class y $.
; vz $f class z $.
;
; ax-eq $a wff ( x = y ) $.
;
; ${
;   $d ph ps $.
;   ax-pair $a wff ( ph ps ) $.
; $}
;
; test5_bad $p wff ( ( x = y ) ( x = z ) ) $=
;   vx vy ax-eq vx vz ax-eq ax-pair
; $.
;
; Verification with metamath-knife:
;   error: Distinct variable violation
;     --> test_dv_05.mm:18:1
;      |
;   18 | / test5_bad $p wff ( ( x = y ) ( x = z ) ) $=
;   19 | |   vx vy ax-eq vx vz ax-eq ax-pair
;   20 | | $.
;      | |__^ Disjoint variable constraint violated
;
; FAILS - {x,y} ∩ {x,z} = {x} ≠ ∅

!(import! &self mmverify-utils)

!(println! "=== TEST 5: Nested Expressions Invalid (FAIL) ===")
!(println! "Complex expressions with overlapping variable sets\n")

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
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_f &kb "vx" "class" "x" 1)
!(add_f &kb "vy" "class" "y" 1)
!(add_f &kb "vz" "class" "z" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)

; Axiom: x = y (no DV)
!(add_a &kb "ax-eq" ("wff" "x" "=" "y"))

; Axiom: ph != ps
!(push-frame &fd)
!(add_d &kb ("ph" "ps") 2)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-pair(x=y, x=z)")
!(println! "First expr vars: {x,y}")
!(println! "Second expr vars: {x,z}")
!(println! "Intersection: {x} - NON-EMPTY!")
!(println! "Expected: DV violation\n")
!(add_p &kb &stack &sp "nested-bad"
  ("wff" "(" "(" "x" "=" "y" ")" "(" "x" "=" "z" ")" ")")
  ("vx" "vy" "ax-eq" "vx" "vz" "ax-eq" "ax-pair") True)

!(pop-frame &kb &fd)
