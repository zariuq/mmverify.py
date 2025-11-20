; Mathematical meaning:
;   Tests a four-argument constructor requiring ALL pairs distinct.
;   The axiom requires 6 pairwise constraints: φ≠ψ, φ≠χ, φ≠θ, ψ≠χ, ψ≠θ, χ≠θ
;   We try (x, y, x, z) - using x in BOTH positions 1 and 3.
;   This violates φ ≠ χ (positions 1 and 3 must be distinct).
;
;   Like: "I need four different fruits. I'm trying apple, orange, apple,
;   banana - but apple appears TWICE (positions 1 and 3), so invalid!"
;
; Metamath equivalent (test_dv_09.mm):
;
; $c wff four ( ) $.
; $v ph ps ch th x y z $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vch $f wff ch $.
; vth $f wff th $.
; vx $f wff x $.
; vy $f wff y $.
; vz $f wff z $.
;
; ${
;   $d ph ps $. $d ph ch $. $d ph th $.
;   $d ps ch $. $d ps th $. $d ch th $.
;   ax-4way $a wff ( ph ps ch th ) $.
; $}
;
; test9_bad $p wff ( x y x z ) $=
;   vx vy vx vz ax-4way
; $.
;
; Verification with metamath-knife:
;   error: Distinct variable violation
;     --> test_dv_09.mm:23:1
;      |
;   23 | / test9_bad $p wff ( x y x z ) $=
;   24 | |   vx vy vx vz ax-4way
;   25 | | $.
;      | |__^ Disjoint variable constraint violated
;
; FAILS - x in positions 1 and 3 violates $d ph ch $.

!(import! &self mmverify-utils)

!(println! "=== TEST 9: Four-Way All-Pairs (FAIL) ===")
!(println! "Four variables with all 6 pairs required disjoint\n")

!(bind! &stack (new-space))
!(bind! &kb (new-space))
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))

!(push-frame &fd)
!(add_c &kb "wff")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "th" 1)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_v &kb "z" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)
!(add_f &kb "wch" "wff" "ch" 1)
!(add_f &kb "wth" "wff" "th" 1)
!(add_f &kb "wx" "wff" "x" 1)
!(add_f &kb "wy" "wff" "y" 1)
!(add_f &kb "wz" "wff" "z" 1)

; Axiom: all 4 variables pairwise disjoint (6 pairs total)
!(push-frame &fd)
!(add_d &kb ("ph" "ps" "ch" "th") 2)
!(add_a &kb "ax-4way" ("wff" "(" "ph" "ps" "ch" "th" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-4way(x, y, x, z) - 'x' in positions 1 and 3")
!(println! "Required: 6 pairwise disjoint pairs")
!(println! "Violates: ph != ch (positions 1 and 3 must be disjoint)")
!(println! "Expected: DV violation\n")
!(add_p &kb &stack &sp "four-bad"
  ("wff" "(" "x" "y" "x" "z" ")")
  ("wx" "wy" "wx" "wz" "ax-4way") True)

!(pop-frame &kb &fd)
