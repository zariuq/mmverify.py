;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metta definitions helpful in transpiling mmverify.py into MeTTa     ;;
;;                                                                     ;;
;;                                                                     ;;
;;                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (empty-space $space) (match $space $atom (remove-atom $space $atom)))

(: match-atom (-> Expression Atom Atom %Undefined$))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (let $pattern $head $rewrite) (empty)))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (match-atom $tail $pattern $rewrite) (empty)))

(= (update-atom $space $atom $update_pattern)
  (match $space $atom (let () (add-atom $space $update_pattern) (remove-atom $space $atom))))

(= (add-subst ($typecode $var))
  (let*
    (
      ($sp (match &wm (sp $sp) $sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      (($entry0 $entry1:) (decons-atom $entry))
    ) (if (== $entry0 $typecode)
        (let* 
          (
            (() (add-atom &subst ($var $entry1:)))
            (() (update-atom &wm (sp $n) (sp (+ $n 1))))
          ) ($var $entry1:))
        (Error ( (sp $sp) (entry $entry) (typecode $typecode) (var $var) ) "Proof stack entry does not match floating hypothesis."))))

; !(update-atom' &wm (sp $n) (sp (+ $n 1)))

(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr)
         (to-list' (cdr-atom $expr) $tail))))

(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

; (: from-list (-> (List $a) Expression))
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

(= (apply_subst_tok $tok)
  (let $res (unify &subst ($tok $sub) $sub $tok) $res))

(= (apply_subst $stmt)
    (flatten-expr (map-atom $stmt $tok (apply_subst_tok $tok))))

(= (check_subst $ehyp)
  (let* 
    (
      ($sp (match &wm (sp $sp) $sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      ($subst_h (apply_subst $ehyp))
    ) (if (== $entry $subst_h)
        (let () (update-atom &wm (sp $n) (sp (+ $n 1))) $subst_h)
        (Error ( (sp $sp) (entry $entry) (ehyp $ehyp) (subst_h $subst_h) ) "Proof stack entry does not match essential hypothesis."))))

;; DV check
(= (map-pairs $list1 $list2 $fn)
   (map-atom $list1 $v1
     (map-atom $list2 $v2
       ($fn $v1 $v2))))

(= (find_vars $stmt)
  (filter-atom $stmt $tok (unify &frames (Var $tok $_) True False)))

(= (orient_pair $x $y)
   (((py-atom min) $x $y) ((py-atom max) $x $y))) 

(= (lookup_d $x $y) (let ($x' $y') (orient_pair $x $y) (unify &frames (DVar ($x' $y') $_) True False)))

(= (dv_check $x $y)
  (if (or
        (== $x $y)
        (not (lookup_d $x $y)))
      (Error ($x $y) "Disjoint variable violation.")
      ()))

; !(match &wm (EHyps $ehyps) (map-atom $ehyps $ehyp (check_subst $ehyp)))

; 2s eval time
; (= (apply_subst_tok $tok $subst)
;   (case ((py-dot $subst get) $tok)
;     ((() $tok) ;; If the token ($tok) is not in the substitution-binding dictionary ($subst), keep it as is.
;     ($sub_tok $sub_tok)) ;; If the token ($tok) is in the dictionry ($subst), then return the substituted token ($sub_tok)
;   ))

; (= (apply_subst $stmt $subst)
;   (map-atom $stmt $tok (apply_subst_tok $tok $subst)))

; 18s eval time
; (= (get-subst (Substitution $subst) $tok)
;   (let ($key $value) (superpose $subst) (if (== $key $tok) $value Empty)))

; (= (apply_subst_tok $subst $tok)
;   (case (get-subst $subst $tok)
;     (( Empty $tok )
;      ( $sub $sub ))))

; (= (apply_subst $stmt $subst)
;   (map-atom $stmt $tok (apply_subst_tok $subst $tok)))

; 16s eval time
;; Somehow broken with both types.  And with none.
; AssertionError: Metta-Py Mismatch! ['term', '0'] != ['get-subst', '{}', 'term', 'get-subst', '{}', '0']
; (: match-atom (-> Expression $a $a $a))
; (: match-atom (-> Expression Atom Atom %Undefined$))
; (= (match-atom $expr $pattern $rewrite)
;    (if-decons-expr $expr $head $tail (let $pattern $head $rewrite) (empty)))
; (= (match-atom $expr $pattern $rewrite)
;    (if-decons-expr $expr $head $tail (match-atom $tail $pattern $rewrite) (empty)))

; (= (get-subst (Substitution $subst) $tok)
;    (match-atom $subst ($tok $sub) $sub))

; (= (apply_subst_tok $subst $tok)
;   (case (get-subst $subst $tok)
;     (( Empty $tok )
;      ( $sub $sub ))))

; (= (apply_subst $stmt $subst)
;   (map-atom $stmt $tok (apply_subst_tok $subst $tok)))

;; 19s
; (: match' (-> (List Atom) $a $a $a))
; (= (match' Nil $pattern $rewrite) (empty))
; (= (match' (Cons $head $tail) $pattern $rewrite) (let $pattern $head $rewrite))
; (= (match' (Cons $head $tail) $pattern $rewrite) (match' $tail $pattern $rewrite))

; (= (to-list $expr)
;    (if (== $expr ()) Nil
;      (Cons (car-atom $expr)
;          (to-list (cdr-atom $expr)))
;    )
; )

; (= (get-subst (Substitution $subst) $tok)
;    (match' (to-list $subst) ($tok $sub) $sub))

; (= (apply_subst_tok $subst $tok)
;   (case (get-subst $subst $tok)
;     (( Empty $tok )
;      ( $sub $sub ))))

; (= (apply_subst $stmt $subst)
;   (map-atom $stmt $tok (apply_subst_tok $subst $tok)))
