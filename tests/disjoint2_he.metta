!(import! &self mmverify-utils)

!(println! "=== Disjoint Variable Test Suite (HE) ===")

!(bind! &kb (new-space))
!(bind! &stack (new-space))
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
!(add_v &kb "w" 1)
!(add_f &kb "xf" "formula" "x" 1)
!(add_f &kb "yf" "formula" "y" 1)
!(add_f &kb "zf" "formula" "z" 1)
!(add_f &kb "wf" "formula" "w" 1)
!(add_a &kb "combo" ("formula" "(" "x" "y" ")"))

!(push-frame &fd)
!(add_d &kb ("x" "y") 2)
!(add_a &kb "ax-1" ("|-" "(" "x" "y" ")"))
!(pop-frame &kb &fd)

!(println! "")
!(println! "Test 1: verybad - Should return Error")
!(add_p &kb &stack &sp "verybad" 
  ("|-" "(" "(" "x" "y" ")" "(" "z" "x" ")" ")")
  ("xf" "yf" "combo" "zf" "xf" "combo" "ax-1") True)

!(println! "")
!(println! "Test 2: good - Should succeed")  
!(push-frame &fd)
!(add_d &kb ("x" "y" "z" "w") 2)
!(add_p &kb &stack &sp "good"
  ("|-" "(" "(" "x" "y" ")" "(" "z" "w" ")" ")")
  ("xf" "yf" "combo" "zf" "wf" "combo" "ax-1") True)
!(pop-frame &kb &fd)

!(pop-frame &kb &fd)
!(println! "")
!(println! "=== Tests complete ===")
