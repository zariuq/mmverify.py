!(import! &self ../../../PeTTa/lib/lib_he)

;; Define matchc exactly as in the utility file
(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

;; Setup data
!(add-atom &self (datum "A"))
!(add-atom &self (datum "B"))
!(add-atom &self (target "A"))

!(println! "=== matchc Scoping Bug Reproduction ===")
!(println! "Setup: (datum A), (datum B), (target A)")
!(println! "Goal: Iterate datums, check if corresponding target exists.")
!(println! "Expected: A -> found, B -> empty")
!(println! "Broken:   A -> found, B -> found (if $x becomes unbound in query)")

!(matchc &self (datum $x)
   (let $res (matchc &self (target $x) found)
     (println! ("Checking" $x "Result:" $res))))
