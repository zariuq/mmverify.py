; Mathematical meaning:
;   Tests a three-argument constructor requiring ALL pairs to be distinct.
;   The axiom requires: φ ≠ ψ, φ ≠ χ, and ψ ≠ χ (pairwise distinct).
;   We use three(θ, τ, η) where all three are explicitly declared distinct.
;   Since all three pairwise constraints are satisfied, this is valid!
;
;   Like: "I need three different fruits. I have apple, orange, banana -
;   all provably different from each other, so I can make the triple."
;
; Metamath equivalent (test_dv_06.mm):
;
; $c wff three $.
; $v ph ps ch th ta et $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vch $f wff ch $.
; vth $f wff th $.
; vta $f wff ta $.
; vet $f wff et $.
;
; $d th ta $. $d th et $. $d ta et $.
;
; ${
;   $d ph ps $. $d ph ch $. $d ps ch $.
;   ax-3way $a wff three ph ps ch $.
; $}
;
; test6_good $p wff three th ta et $=
;   vth vta vet ax-3way
; $.
;
; Verification with metamath-knife:
;   0 diagnostics issued.
;
; PASSES - all 3 pairs explicitly declared disjoint.

!(import! &self mmverify-utils)

!(println! "=== TEST 6: Three-Way Valid (PASS) ===")
!(println! "Three pairwise DV constraints, all satisfied\n")

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
!(add_v &kb "ta" 1)
!(add_v &kb "et" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)
!(add_f &kb "wch" "wff" "ch" 1)
!(add_f &kb "wth" "wff" "th" 1)
!(add_f &kb "wta" "wff" "ta" 1)
!(add_f &kb "wet" "wff" "et" 1)

; CRITICAL: Declare th, ta, et all pairwise disjoint
!(add_d &kb ("th" "ta" "et") 1)

; Axiom: ph != ps AND ph != ch AND ps != ch (all pairs)
!(push-frame &fd)
!(add_d &kb ("ph" "ps" "ch") 2)
!(add_a &kb "ax-3way" ("wff" "(" "ph" "ps" "ch" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-3way(th, ta, et)")
!(println! "Declared: th, ta, et all pairwise disjoint")
!(println! "Expected: SUCCESS\n")
!(add_p &kb &stack &sp "three-good"
  ("wff" "(" "th" "ta" "et" ")")
  ("wth" "wta" "wet" "ax-3way") True)

!(println! "✓ Test completed successfully")

!(pop-frame &kb &fd)
