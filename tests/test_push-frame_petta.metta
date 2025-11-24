!(import! &self ../mmverify-utils_petta)

; Test utility function
(= (check-equal $actual $expected)
   (if (== $actual $expected)
       (println! (✅ (quote $actual) is (quote $expected)))
       (println! (❌ (quote $actual) is $actual should-be $expected))))

!(println! "=== Testing push-frame ===")
!(println! "")

; Test 1: Push from 0 to 1
!(println! "Test 1: Push from 0 to 1")
!(bind! &fd (new-state 0))
!(push-frame &fd)
!(check-equal (get-state &fd) 1)

; Test 2: Push from 5 to 6
!(println! "Test 2: Push from 5 to 6")
!(bind! &fd2 (new-state 5))
!(push-frame &fd2)
!(check-equal (get-state &fd2) 6)
