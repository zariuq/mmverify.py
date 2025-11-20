; Mathematical meaning:
;   Baseline test: an axiom with NO distinctness requirements.
;   The axiom just takes any proposition, with no constraints.
;   So nocnstr(φ) is valid, and even nocnstr(φ, φ) would be valid.
;   This shows that DV checking only applies when explicitly required.
;
;   Like: "Make a list of any fruits you want, duplicates allowed -
;   so apple, apple, apple is perfectly fine!"
;
; Metamath equivalent (test_dv_08.mm):
;
; $c wff nocnstr $.
; $v ph $.
;
; vph $f wff ph $.
;
; ax-no-dv $a wff nocnstr ph $.
;
; test8_good $p wff nocnstr ph $=
;   vph ax-no-dv
; $.
;
; Verification with metamath-knife:
;   0 diagnostics issued.
;
; PASSES - no DV constraints means any substitution is valid.

!(import! &self mmverify-utils)

!(println! "=== TEST 8: No Constraints Baseline (PASS) ===")
!(println! "Axiom with NO DV constraints accepts any substitution\n")

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

; Axiom with NO DV constraints
!(add_a &kb "ax-no-dv" ("wff" "(" "ph" "ps" ")"))

!(println! "Proof: ax-no-dv(ph, ph) - same variable twice")
!(println! "No DV constraints on axiom")
!(println! "Expected: SUCCESS (no violation possible)\n")
!(add_p &kb &stack &sp "no-dv"
  ("wff" "(" "ph" "ph" ")")
  ("wph" "wph" "ax-no-dv") True)

!(println! "✓ Test completed successfully")

!(pop-frame &kb &fd)
