; Mathematical meaning:
;   We have an axiom that constructs a pair from two DISTINCT propositions.
;   We explicitly declare that χ (chi) and θ (theta) are different variables.
;   So pair(χ, θ) is valid - we're using two provably distinct propositions.
;
;   This is like saying: "I have an apple and an orange, both confirmed
;   to be different fruits, so I can make a fruit pair."
;
; Metamath equivalent (test_dv_02.mm):
;
; $c wff pair $.
; $v ph ps ch th $.
;
; vph $f wff ph $.
; vps $f wff ps $.
; vch $f wff ch $.
; vth $f wff th $.
;
; $d ch th $.  ; Explicit declaration
;
; ${
;   $d ph ps $.
;   ax-pair $a wff pair ph ps $.
; $}
;
; test2_good $p wff pair ch th $=
;   vch vth ax-pair
; $.
;
; Verification with metamath-knife:
;   0 diagnostics issued.
;
; PASSES - confirms explicit DV declaration enables valid proofs.

!(import! &self mmverify-utils)

!(println! "=== TEST 2: Different Variables (PASS) ===")
!(println! "Different variables with explicit DV declaration\n")

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
!(add_f &kb "wph" "wff" "ph" 1)
!(add_f &kb "wps" "wff" "ps" 1)
!(add_f &kb "wch" "wff" "ch" 1)
!(add_f &kb "wth" "wff" "th" 1)

; CRITICAL: Declare ch != th
!(add_d &kb ("ch" "th") 1)

; Axiom: ph != ps
!(push-frame &fd)
!(add_d &kb ("ph" "ps") 2)
!(add_a &kb "ax-pair" ("wff" "(" "ph" "ps" ")"))
!(pop-frame &kb &fd)

!(println! "Proof: ax-pair(ch, th)")
!(println! "Declared: ch != th")
!(println! "Expected: SUCCESS\n")
!(add_p &kb &stack &sp "good1"
  ("wff" "(" "ch" "th" ")")
  ("wch" "wth" "ax-pair") True)

!(println! "✓ Test completed successfully")

!(pop-frame &kb &fd)
