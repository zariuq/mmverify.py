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

; 2s eval time
(= (apply_subst_tok $tok $subst)
  (case ((py-dot $subst get) $tok)
    ((() $tok) ;; If the token ($tok) is not in the substitution-binding dictionary ($subst), keep it as is.
    ($sub_tok $sub_tok)) ;; If the token ($tok) is in the dictionry ($subst), then return the substituted token ($sub_tok)
  ))

(= (apply_subst $stmt $subst)
  (map-atom $stmt $tok (apply_subst_tok $tok $subst)))

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
