; Test: Type mismatch error - tze produces "term 0" but wim expects "wff P"
;
; metamath-knife error:
;   error: Wrong floating typecode
;   --> test_type_mismatch.mm:25:1
;   bad $p wff ( 0 -> 0 ) $= tze tze wim $.
;   Step used for $f hypothesis does not match typecode
;
; Expected: PeTTa should return an Error indicating type mismatch

!(bind! &sp (new-state -1))
!(bind! &fd (new-state 0))
!(import! &self ../mmverify-utils_petta)
!(push-frame &fd)
!(add_c &kb "term")
!(add_c &kb "wff")
!(add_c &kb "|-")
!(add_c &kb "0")
!(add_c &kb "(")
!(add_c &kb ")")
!(add_c &kb "->")
!(add_v &kb "t" 1)
!(add_v &kb "r" 1)
!(add_v &kb "P" 1)
!(add_v &kb "Q" 1)
!(add_f &kb "tt" "term" "t" 1)
!(add_f &kb "tr" "term" "r" 1)
!(add_f &kb "wp" "wff" "P" 1)
!(add_f &kb "wq" "wff" "Q" 1)
!(add_a &kb "tze" ("term" "0"))
!(add_a &kb "wim" ("wff" "(" "P" "->" "Q" ")"))

; BAD PROOF: tze gives (term 0) but wim needs (wff P) and (wff Q)
; This should fail with type mismatch error
!(add_p &kb &stack &sp "bad" ("wff" "(" "0" "->" "0" ")") ("tze" "tze" "wim") True)
!(pop-frame &kb &fd)
