; Test that stack is properly cleaned between proofs
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))
!(import! &self ../mmverify-utils_petta)
!(push-frame &fd)

; Add constants and variables
!(add_c &kb "term")
!(add_c &kb "|-")
!(add_v &kb "A" 1)
!(add_v &kb "B" 1)
!(add_v &kb "C" 1)
!(add_f &kb "ta" "term" "A" 1)
!(add_f &kb "tb" "term" "B" 1)
!(add_f &kb "tc" "term" "C" 1)

; Add axioms
!(add_a &kb "ax1" ("|-" "A"))
!(add_a &kb "ax2" ("|-" "B"))

; First proof - should succeed and leave only one item on stack
!(add_p &kb &stack &sp "proof1" ("|-" "A") ("ta" "ax1") True)

; Check that stack was cleaned - second proof should also have exactly one item
; If stack wasn't cleaned, this would fail with "Stack has more than one entry"
!(add_p &kb &stack &sp "proof2" ("|-" "B") ("tb" "ax2") True)

; Third proof to triple-check
!(add_p &kb &stack &sp "proof3" ("|-" "A") ("ta" "ax1") True)

!(pop-frame &kb &fd)
!(println! "✅ Stack cleanup test passed")
