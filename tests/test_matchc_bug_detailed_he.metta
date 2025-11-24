
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

!(println! "--- TEST 1: Nested matchc (Original Bug) ---")
!(matchc &self (datum $x)
   (let $res (matchc &self (target $x) found)
     (println! ("Checking" $x "Result:" $res))))

!(println! "--- TEST 2: matchc + match (Mixed) ---")
!(matchc &self (datum $x)
   (let $res (collapse (match &self (target $x) found))
     (println! ("Checking" $x "Result:" $res))))

!(println! "--- TEST 3: match + matchc (Mixed) ---")
!(collapse (match &self (datum $x)
   (let $res (matchc &self (target $x) found)
     (println! ("Checking" $x "Result:" $res)))))

!(println! "--- TEST 4: match + match (Inlined - Correct) ---")
!(collapse (match &self (datum $x)
   (let $res (collapse (match &self (target $x) found))
     (println! ("Checking" $x "Result:" $res)))))
