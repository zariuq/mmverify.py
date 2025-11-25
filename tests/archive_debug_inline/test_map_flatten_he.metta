; Test map-atom + flatten behavior

(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr) (to-list (cdr-atom $expr)))))

(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr) (to-list' (cdr-atom $expr) $tail))))

(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail) (cons-atom $head $tail-list)))

(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

!(println! "Testing on simple expression without map-atom:")
!(println! "Original: (wff x = y)")
!(println! "to-list:" (to-list (wff x = y)))
!(println! "flatten-list:" (flatten-list (to-list (wff x = y))))
!(println! "from-list:" (from-list (flatten-list (to-list (wff x = y)))))
!(println! "flatten-expr:" (flatten-expr (wff x = y)))

!(println! "\nTesting on expression with nested parts:")
!(println! "Original: (wff (P -> Q))")
!(println! "to-list:" (to-list (wff (P -> Q))))
!(println! "flatten-list:" (flatten-list (to-list (wff (P -> Q)))))
!(println! "from-list:" (from-list (flatten-list (to-list (wff (P -> Q))))))
!(println! "flatten-expr:" (flatten-expr (wff (P -> Q))))
