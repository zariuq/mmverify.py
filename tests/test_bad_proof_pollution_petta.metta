!(import! &self ../mmverify-utils_petta)

!(println! "=== Test: Bad Proofs Should NOT Pollute Knowledge Base ===")

!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))

; Setup
!(add_c &kb "formula")
!(add_c &kb "|-")
!(add_c &kb "(")
!(add_c &kb ")")

!(push-frame &fd)
!(add_v &kb "x" 1)
!(add_v &kb "y" 1)
!(add_v &kb "z" 1)
!(add_f &kb "xf" "formula" "x" 1)
!(add_f &kb "yf" "formula" "y" 1)
!(add_f &kb "zf" "formula" "z" 1)
!(add_a &kb "combo" ("formula" "(" "x" "y" ")"))

!(push-frame &fd)
!(add_d &kb ("x" "y") 2)
!(add_a &kb "ax-1" ("|-" "(" "x" "y" ")"))
!(pop-frame &kb &fd)

!(println! "")
!(println! "Step 1: Check KB before adding bad proof")
!(println! "Looking for label 'badproof':")
!(println! (collapse (match &kb ((Label "badproof") $type $rest) found)))

!(println! "")
!(println! "Step 2: Try to add BAD proof (should fail with DV error)")
!(bind! $result (add_p &kb &stack &sp "badproof" 
  ("|-" "(" "(" "x" "y" ")" "(" "z" "x" ")" ")")
  ("xf" "yf" "combo" "zf" "xf" "combo" "ax-1") True))
!(println! (Result: $result))

!(println! "")
!(println! "Step 3: Check KB after adding bad proof")
!(println! "Test: Checking if 'badproof' label exists in KB")

; Direct test: try to match badproof
; If match succeeds, a message will print
; If match fails, no message prints
!(println! "Attempting to find badproof...")
!(match &kb ((Label "badproof") $type $rest)
    (println! "❌ FAIL: Bad proof WAS added to KB (pollution!)"))

; If we reach here without printing FAIL, print PASS
!(println! "If no FAIL above, then:")
!(println! "✅ PASS: Bad proof was NOT added to KB")

!(pop-frame &kb &fd)
