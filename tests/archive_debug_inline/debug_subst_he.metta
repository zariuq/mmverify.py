; Debug substitution issues

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

(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

(= (apply_subst $subst $stmt)
    (flatten-expr (map-atom $stmt $tok (apply_subst_tok $subst $tok))))

!(println! "Test what map-atom does to (wff x = y):")
!(bind! &subst (new-space))
!(map-atom (wff x = y) $tok (println! $tok))

!(println! "\nTest apply_subst_tok on each token:")
!(println! (apply_subst_tok &subst wff))
!(println! (apply_subst_tok &subst x))
!(println! (apply_subst_tok &subst =))
!(println! (apply_subst_tok &subst y))

!(println! "\nTest what map-atom produces:")
!(println! (map-atom (wff x = y) $tok (apply_subst_tok &subst $tok)))

!(println! "\nTest to-list on map-atom result:")
!(println! (to-list (map-atom (wff x = y) $tok (apply_subst_tok &subst $tok))))

!(println! "\nTest flatten-list:")
!(println! (flatten-list (to-list (map-atom (wff x = y) $tok (apply_subst_tok &subst $tok)))))

!(println! "\nTest from-list:")
!(println! (from-list (flatten-list (to-list (map-atom (wff x = y) $tok (apply_subst_tok &subst $tok))))))

!(println! "\nFull apply_subst:")
!(println! (apply_subst &subst (wff x = y)))
