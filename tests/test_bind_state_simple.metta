!(println! "Testing if bind! works with new-state in PeTTa...")

!(bind! &mystate (new-state 42))
!(println! ("State value:" (get-state &mystate)))
!(change-state! &mystate 100)
!(println! ("After change:" (get-state &mystate)))

!(println! "Done!")
