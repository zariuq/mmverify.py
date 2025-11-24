!(println! "Testing string vs atom equality in PeTTa")
!(println! "")

!(add-atom &self (test1 (Value "hello")))
!(add-atom &self (test2 (Value hello)))

!(println! "test1 stored with string \"hello\":")
!(match &self (test1 (Value $x)) (println! ("  value:" $x "  type:" (get-type $x))))

!(println! "test2 stored with atom hello:")
!(match &self (test2 (Value $x)) (println! ("  value:" $x "  type:" (get-type $x))))

!(println! "")
!(println! "Does test1 match (Value \"hello\")?")
!(println! (collapse (match &self (test1 (Value "hello")) yes)))

!(println! "Does test1 match (Value hello)?")
!(println! (collapse (match &self (test1 (Value hello)) yes)))

!(println! "Does test2 match (Value \"hello\")?")
!(println! (collapse (match &self (test2 (Value "hello")) yes)))

!(println! "Does test2 match (Value hello)?")
!(println! (collapse (match &self (test2 (Value hello)) yes)))

!(println! "")
!(println! "String equality test:")
!(println! ("\"hello\" == \"hello\":" (== "hello" "hello")))
!(println! ("hello == hello:" (== hello hello)))
!(println! ("\"hello\" == hello:" (== "hello" hello)))
