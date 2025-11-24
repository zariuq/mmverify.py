; MeTTa version of push-frame
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &fd (new-state 0))
!(push-frame &fd)
!(assertEqual (get-state &fd) 1)

; Test 2: Push from 5 to 6
!(bind! &fd2 (new-state 5))
!(push-frame &fd2)
!(assertEqual (get-state &fd2) 6)
