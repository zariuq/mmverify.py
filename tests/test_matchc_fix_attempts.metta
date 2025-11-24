!(import! &self ../../../PeTTa/lib/lib_he)

;; Standard definition (BROKEN for variable sharing)
;; (= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

;; ATTEMPT 1: Type annotations
;; Force arguments to be Expressions or Atoms to prevent premature evaluation?
;; But the issue isn't evaluation, it's variable unification across arguments.
(= (matchc-typed (: $space Space) (: $pattern Atom) (: $query Atom)) 
   (collapse (match $space $pattern $query)))

;; ATTEMPT 2: Using `let` to bind variables before match?
;; No, we can't bind variables we don't know about.

;; ATTEMPT 3: Using `function` (minimal MeTTa) if available?
;; (= (matchc-fun $s $p $q) (collapse (match $s $p (eval $q)))) 
;; Does eval help? No, if $q has unbound vars, eval just evals it with unbound vars.

;; ATTEMPT 4: Quote the query?
;; (= (matchc-quote $s $p $q) (collapse (match $s $p (eval $q))))
;; Caller: (matchc-quote &self (datum $x) (quote (println! $x)))
;; PeTTa doesn't support `quote` standardly yet?

!(add-atom &self (datum "A"))

!(println! "--- CONTROL: Standard matchc (Broken) ---")
(= (matchc $s $p $q) (collapse (match $s $p $q)))
!(matchc &self (datum $x) (println! ("Control" $x)))

!(println! "--- ATTEMPT 1: Typed matchc ---")
!(matchc-typed &self (datum $x) (println! ("Typed" $x)))

!(println! "--- ATTEMPT 5: Explicit unification check ---")
;; This checks if the variable object identity is preserved
(= (check-vars $a $b) 
   (if (== $a $b) (println! "Same") (println! "Different")))
!(check-vars $x $x) 
