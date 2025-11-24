!(println! "=== Testing size-atom in PeTTa ===")

; Test what size-atom returns
!(println! ("size-atom on x:" (size-atom x)))
!(println! ("size-atom on hello:" (size-atom hello)))
!(println! ("size-atom on (a b c):" (size-atom (a b c))))

; Test repr
!(println! ("repr x:" (repr x)))
!(println! ("size-atom (repr x):" (size-atom (repr x))))
