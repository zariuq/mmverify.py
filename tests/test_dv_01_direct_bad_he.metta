; Mathematical meaning:
;   We have an axiom that constructs a pair from two DISTINCT propositions.
;   This test tries to use the SAME proposition φ twice: pair(φ, φ)
;   This violates the distinctness requirement, so it must fail.
;
;   Think of it like: "You can't make a pair of apples and oranges using
;   two apples - they must be different fruits!"
;
; Metamath equivalent (test_dv_01.mm):
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
; test1_bad $p wff pair ph ph $=
;   vph vph ax-pair
; $.
;
; Verification with metamath-knife:
;   error: Distinct variable violation
;     --> test_dv_01.mm:13:1
;      |
;   13 | / test1_bad $p wff pair ph ph $=
;   14 | |   vph vph ax-pair
;   15 | | $.
;      | |__^ Disjoint variable constraint violated
;
; This confirms the MeTTa implementation matches Metamath semantics.

!(import! &self mmverify-utils)

!(println! "=== TEST 1: Direct Collision (FAIL) ===")
!(println! "Same variable used twice violates DV constraint\n")

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

!(println! "Proof: ax-pair(ph, ph)")
!(println! "Expected: DV violation\n")
!(add_p &kb &stack &sp "bad1"
  ("wff" "(" "ph" "ph" ")")
  ("wph" "wph" "ax-pair") True)

!(pop-frame &kb &fd)
