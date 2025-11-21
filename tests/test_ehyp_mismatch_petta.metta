; Test: Essential hypothesis mismatch error
;
; metamath-knife error:
;   error: Wrong essential statement
;   --> test_ehyp_mismatch.mm:51:1
;   bad1 $p |- Q $= wp wq wq ax-q wp wq ax-pq mp $.
;   Step used for $e hypothesis does not match statement
;
; Expected: PeTTa should return Error for bad1, success for good

!(bind! &stack (new-space))
!(bind! &kb (new-space))
!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))
!(import! &self ../mmverify-utils_petta)
!(push-frame &fd)
!(add_c &kb "wff")
!(add_c &kb "|-")
!(add_c &kb "(")
!(add_c &kb ")")
!(add_c &kb "->")
!(add_v &kb "P" 1)
!(add_v &kb "Q" 1)
!(add_f &kb "wp" "wff" "P" 1)
!(add_f &kb "wq" "wff" "Q" 1)
!(add_a &kb "wim" ("wff" "(" "P" "->" "Q" ")"))
!(add_a &kb "ax-p" ("|-" "P"))
!(add_a &kb "ax-q" ("|-" "Q"))
!(add_a &kb "ax-pq" ("|-" "(" "P" "->" "Q" ")"))
!(add_a &kb "ax-qp" ("|-" "(" "Q" "->" "P" ")"))
!(push-frame &fd)
!(add_e &kb "min" ("|-" "P") 2)
!(add_e &kb "maj" ("|-" "(" "P" "->" "Q" ")") 2)
!(add_a &kb "mp" ("|-" "Q"))
!(pop-frame &kb &fd)

; GOOD proof - should succeed
!(add_p &kb &stack &sp "good" ("|-" "Q") ("wp" "wq" "wp" "ax-p" "wp" "wq" "ax-pq" "mp") True)

; BAD proof - provides ax-q (|- Q) where min expects (|- P)
; Should fail with essential hypothesis mismatch
!(add_p &kb &stack &sp "bad1" ("|-" "Q") ("wp" "wq" "wq" "ax-q" "wp" "wq" "ax-pq" "mp") True)
!(pop-frame &kb &fd)
