!(import! &self ../../../PeTTa/lib/lib_he)

!(println! ("type of match:" (get-type match)))

; ;; Define matchc exactly as in the utility file
; (: matchc (-> Expression Atom Atom %Undefined%))
; (= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))


; "if you can get away with just match: you get 200x the speed of H-E nested matching"
(: matchf (-> %Undefined% Expression Expression %Undefined%))
(= (matchf $space $pattern $query)
   (match $space $pattern (eval $query)))

(: matchc (-> %Undefined% Expression Expression %Undefined%))
(= (matchc $space $pattern $query)
   (collapse (matchf $space $pattern $query)))

; !(hide (matchc &self (friend $1 $2)
;               (matchc &self (friend $2 $3) 
;                      ((add-atom &self (transitive $1 $2 $3))
;                       (remove-atom &self (friend $1 $2))
;                       (remove-atom &self (friend $2 $3))))))

(friend tim tom)

(= (thanksroman $f) ($f 42))
(= (f $x) $x)

!(thanksroman f)

!(matchc &self (friend $a $b) (friend $a $b))

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
