; Simplified treat_assertion test to debug

(= (test $actual $expected) (assertEqual $actual $expected))
(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

; Test 1: Just check if FHyps are read correctly
!(println! "Test: Stack reading with tpl")
!(bind! &stack (new-space))
!(bind! &sp (new-state 0.0))

; For tpl with 2 FHyps, we need stack_len=2, npop=2, so sp_val=0
; FHyps should be read from position 0 and 1
!(add-atom &stack ((Num 0) ("term" "t")))
!(add-atom &stack ((Num 1) ("term" "0")))

!(println! "Stack before:")
!(println! (matchc &stack $s $s))

; Set sp to 0
!(change-state! &sp 0.0)
!(println! (Initial sp: (get-state &sp)))

; Try to read first entry
!(let $sp_val (get-state &sp)
  (let $entry (match &stack ((Num $sp_val) $s) $s)
    (println! (Entry at $sp_val: $entry))))

!(println! "Done")
