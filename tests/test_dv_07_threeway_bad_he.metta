; Mathematical meaning:
;   Tests a three-argument constructor with a violation.
;   The axiom requires: φ ≠ ψ, φ ≠ χ, and ψ ≠ χ (all pairwise distinct).
;   We try three(x, x, y) - using x in BOTH first and second positions.
;   This violates the φ ≠ ψ constraint, so it must fail!
;
;   Like: "I need three different fruits, but I'm trying to use
;   apple, apple, orange - the first two are the SAME, so invalid!"
;
; Metamath equivalent (test_dv_07.mm):
;
; $c wff three $.
; $v ph ps ch x y $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vch $f wff ch $.
; vx $f wff x $.
; vy $f wff y $.
;
; ${
;   $d ph ps $. $d ph ch $. $d ps ch $.
;   ax-3way $a wff three ph ps ch $.
; $}
;
; test7_bad $p wff three x x y $=
;   vx vx vy ax-3way
; $.
;
; Verification with metamath-knife:
;   error: Distinct variable violation
;     --> test_dv_07.mm:18:1
;      |
;   18 | / test7_bad $p wff three x x y $=
;   19 | |   vx vx vy ax-3way
;   20 | | $.
;      | |__^ Disjoint variable constraint violated
;
; FAILS - x appears in positions 1 and 2, violates $d ph ps $.

!(import! &self mmverify-utils)

!(println! "=== TEST 7: Three-Way Invalid (FAIL) ===")
!(println! "Three pairwise DV constraints, one violated\n")

!(bind! &stack (new-space))
!(bind! &kb (new-space))
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))

!(push-frame &fd)
!(add_c &kb "wff")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_v &kb "ch" 1)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)
!(add_f &kb "wch" "wff" "ch" 1)
!(add_f &kb "wx" "wff" "x" 1)
!(add_f &kb "wy" "wff" "y" 1)

; Axiom: ph != ps AND ph != ch AND ps != ch (all pairs)
!(push-frame &fd)
!(add_d &kb ("ph" "ps" "ch") 2)
!(add_a &kb "ax-3way" ("wff" "(" "ph" "ps" "ch" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-3way(x, x, y) - first two args same!")
!(println! "Required: all three pairwise disjoint")
!(println! "Violates: ph != ps (positions 1 and 2)")
!(println! "Expected: DV violation\n")
!(add_p &kb &stack &sp "three-bad"
  ("wff" "(" "x" "x" "y" ")")
  ("wx" "wx" "wy" "ax-3way") True)

!(pop-frame &kb &fd)
