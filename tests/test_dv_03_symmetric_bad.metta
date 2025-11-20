; Mathematical meaning:
;   Tests that distinctness is symmetric: if φ ≠ ψ, then ψ ≠ φ.
;   The axiom says φ and ψ must be distinct.
;   This test tries pair(ψ, ψ) - using ψ twice.
;   Even though the constraint is written as "φ ≠ ψ", it applies symmetrically.
;
;   Like: "If apples must differ from oranges, then oranges must differ
;   from apples - you still can't make a pair from two oranges!"
;
; Metamath equivalent (test_dv_03.mm):
;
; $c wff pair $.
; $v ph ps $.
;
; vph $f wff ph $.
; vps $f wff ps $.
;
; ${
;   $d ph ps $.
;   ax-pair $a wff pair ph ps $.
; $}
;
; test3_bad $p wff pair ps ps $=
;   vps vps ax-pair
; $.
;
; Verification with metamath-knife:
;   error: Distinct variable violation
;     --> test_dv_03.mm:13:1
;      |
;   13 | / test3_bad $p wff pair ps ps $=
;   14 | |   vps vps ax-pair
;   15 | | $.
;      | |__^ Disjoint variable constraint violated
;
; DV constraints are symmetric: $d ph ps $. means both directions.

!(import! &self mmverify-utils)

!(println! "=== TEST 3: Symmetric Violation (FAIL) ===")
!(println! "DV constraints are symmetric: ph != ps means ps != ph\n")

!(bind! &stack (new-space))
!(bind! &kb (new-space))
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))

!(push-frame &fd)
!(add_c &kb "wff")
!(add_v &kb "ph" 1)
!(add_v &kb "ps" 1)
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)

; Axiom: ph != ps
!(push-frame &fd)
!(add_d &kb ("ph" "ps") 2)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-pair(ps, ps)")
!(println! "DV constraint: ph != ps")
!(println! "Testing symmetry: ps != ph should also hold")
!(println! "Expected: DV violation\n")
!(add_p &kb &stack &sp "sym-bad"
  ("wff" "(" "ps" "ps" ")")
  ("wps" "wps" "ax-pair") True)

!(pop-frame &kb &fd)
