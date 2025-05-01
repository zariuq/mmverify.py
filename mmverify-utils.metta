;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metta definitions helpful in transpiling mmverify.py into MeTTa     ;;
;;                                                                     ;;
;;                                                                     ;;
;;                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (: transform (-> Atom Atom %Undefined%))
; (: transform_ (-> Atom Atom %Undefined%))
; (= (transform_ $pattern $query) (match &self $pattern (let $_ (add-atom &self $query) $query)))
; (= (transform $pattern $query) (match &self $pattern $query))
; (= (? $pattern) (transform $pattern $pattern))

(: umatch (-> hyperon::space::DynSpace Atom Atom %Undefined%))
(= (umatch $space $pattern $query) (unique (case (match $space $pattern $query) ( (Empty () ) ( () () ) ))))

; (= (empty-space $space) (match $space $atom (remove-atom $space $atom)))
; (= (empty-space2 $space) (unify $space $atom (remove-atom $space $atom) ())) ;; Doesn't work at all
; (= (empty-space $space) (unique (case (match $space $atom (remove-atom $space $atom)) ( (Empty () ) ( () () ) ))))
(= (empty-space $space) (umatch $space $atom (remove-atom $space $atom)))

(= (remove-pattern $space $pattern) (match $space $pattern (remove-atom $space $pattern)))

(= (remove_from_stack $stack_ptr $stack_len)
  (if (> $stack_len $stack_ptr)
    (let () (match &stack ( (Num $stack_ptr) $s ) (remove-atom &stack ( (Num $stack_ptr) $s ))) (remove_from_stack (+ 1 $stack_ptr) $stack_len))
    ()))

(: match-atom (-> Expression Atom Atom %Undefined$))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (let $pattern $head $rewrite) (empty)))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (match-atom $tail $pattern $rewrite) (empty)))

(= (update-atom $space $atom $update_pattern)
  (match $space $atom (let () (add-atom $space $update_pattern) (remove-atom $space $atom))))

; (= (add-subst ($typecode $var))
;   (let*
;     (
;       ($sp (match &wm (sp $sp) $sp))
;       ($entry (match &stack ((Num $sp) $s) $s))
;       (($entry0 $entry1:) (decons-atom $entry))
;     ) (if (== $entry0 $typecode)
;         (let* 
;           (
;             (() (add-atom &subst ($var $entry1:)))
;             (() (update-atom &wm (sp $n) (sp (+ $n 1))))
;           ) ($var $entry1:))
;         (Error ( (sp $sp) (entry $entry) (typecode $typecode) (var $var) ) "Proof stack entry does not match floating hypothesis."))))

(= (add-subst $subst ($typecode $var))
  (let*
    (
      ($sp (match &wm (sp $sp) $sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      (($entry0 $entry1:) (decons-atom $entry))
    ) (if (== $entry0 $typecode)
        (let* 
          (
            (() (add-atom $subst ($var $entry1:)))
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

; (= (apply_subst_tok $tok)
;   (let $res (unify &subst ($tok $sub) $sub $tok) $res))

; (= (apply_subst $stmt)
;     (flatten-expr (map-atom $stmt $tok (apply_subst_tok $tok))))

; (= (check_subst $ehyp)
;   (let* 
;     (
;       ($sp (match &wm (sp $sp) $sp))
;       ($entry (match &stack ((Num $sp) $s) $s))
;       ($subst_h (apply_subst $ehyp))
;     ) (if (== $entry $subst_h)
;         (let () (update-atom &wm (sp $n) (sp (+ $n 1))) $subst_h)
;         (Error ( (sp $sp) (entry $entry) (ehyp $ehyp) (subst_h $subst_h) ) "Proof stack entry does not match essential hypothesis."))))

(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

(= (apply_subst $subst $stmt)
    (flatten-expr (map-atom $stmt $tok (apply_subst_tok $subst $tok))))

(= (check_subst $subst $ehyp)
  (let* 
    (
      ($sp (match &wm (sp $sp) $sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      ($subst_h (apply_subst $subst $ehyp))
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

; (= (check_dvs $dvs0)
;     (map-atom $dvs0 $d 
;       (let ($d1 $d2) $d ;; the for x, y in dvs0
;       (let ($x_vars $y_vars)
;           (match &subst ($d1 $sub1) 
;           (match &subst ($d2 $sub2) 
;               ((find_vars $sub1) (find_vars $sub2)))) 
;       (map-pairs $x_vars $y_vars dv_check)))))

(= (check_dvs $subst $dvs0)
    (map-atom $dvs0 $d 
      (let ($d1 $d2) $d ;; the for x, y in dvs0
      (let ($x_vars $y_vars)
          (match $subst ($d1 $sub1) 
          (match $subst ($d2 $sub2) 
              ((find_vars $sub1) (find_vars $sub2)))) 
      (map-pairs $x_vars $y_vars dv_check)))))

;; treat_step outputs non-deterministically ## To debug
(= (treat_assertion $label $Data $stack_len)
    (let*
      (
        ($dvars (match-atom $Data (DVars $dvars) $dvars ))
        ($fhyps (match-atom $Data (FHyps $fhyps) $fhyps ))
        ($ehyps (match-atom $Data (EHyps $ehyps) $ehyps ))
        ($statement (match-atom $Data (Statement $statement) $statement ))
        ; ($dvs0' (match-atom $Data (DVars $dvars) $dvars)) ;; Looks like the vars are matched from the above statements, so it's all good?
        ; ($fhyps' (match-atom $Data (FHyps $fhyps) $fhyps))
        ; ($ehyps' (match-atom $Data (EHyps $ehyps) $ehyps))
        ; ($stmt' (match-atom $Data (Statement $statement) $statement))
        (() (println! (assertion data: $dvars $fhyps $ehyps $statement)))
        ; ($lf (match &wm (FHyps $fhyps) (size-atom $fhyps)))
        ; ($le (match &wm (EHyps $ehyps) (size-atom $ehyps)))
        ($lf (size-atom $fhyps))
        ($le (size-atom $ehyps))
        (() (println! (new lf $lf and new le $le)))
        ($npop (+ $lf $le))
        ; ($ls (case (collapse (match &stack ( (Num $n) $s ) $n)) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) ))) 
        ($sp (- $stack_len $npop))
        (() (println! (stack_len: $stack_len , npop: $npop , sp: $sp , if_comp: (< $sp 0))))
        (() (if (< $sp 0) (Error ((label $label) (npop $npop)) "Stack underflow: proof step requires too many hypotheses") ()))
        (() (println! "Eval test 1 & 2"))
        ; (() (add-atom &wm (npop $npop))) ;; Seems unused
        (() (add-atom &wm (sp $sp)))
        (() (println! "Eval test 3"))
        ; (() (empty-space &subst))
        ($subst (new-space))
        ; ($subst &subst)
        (() (println! ("Eval test 4" fhyps: $fhyps)))
        ($_subst_list (map-atom $fhyps $fhyp (add-subst $subst $fhyp)))
        ; ($_subst_list (match &wm (FHyps $fhyps) (map-atom $fhyps $fhyp (add-subst $fhyp))))
        (() (println! (substs: $_subst_list)))
        (() (println! ("Eval test 5" ehyps: $ehyps)))
        ($_empty_return_values1 (map-atom $ehyps $ehyp (check_subst $subst $ehyp))) ;; Not sure how to match [() () ()], lol 
        ; ($_empty_return_values1 (match &wm (EHyps $ehyps) (map-atom $ehyps $ehyp (check_subst $ehyp)))) ;; Not sure how to match [() () ()], lol
        (() (println! "Eval test 6"))
        ($_empty_return_values2 (check_dvs $subst $dvars))
        (() (println! (check_dvs: $_empty_return_values2)))
        (() (println! "Eval test 7"))
        ; (() (remove_from_stack $sp $stack_len)) ;; This version seems slower than the one with unique.
        (() (unique (match &stack ( (Num $n) $s ) (if (>= $n $sp) (remove-atom &stack ( (Num $n) $s )) ())))) ;; I think this is the line introducing weird non-determinism in, lol, which order to remove the stack entries?
        (() (println! "Eval test 8"))
        ($new_conclusion (let $new_conclusion (apply_subst $subst $statement) (let () (add-atom &stack ((Num $sp) $new_conclusion)) $new_conclusion)))
        ; ($new_conclusion (let $new_conclusion (match &wm (Statement $stmt) (apply_subst $stmt)) (let () (add-atom &stack ((Num $sp) $new_conclusion)) $new_conclusion)))
        (() (println! (new_conclusion: $new_conclusion)))
        ; (() (remove-pattern &wm (sp $sp)))
        (() (empty-space &wm))
      ) ())) ;;($dvars $fhyps $ehyps $statement $lf $le $npop $stack_len $sp $_subst_list $new_conclusion)))

(= (treat_hypothesis $label $Type $Data $stack_len)
  (unify &frames (ActiveHyp $label) 
    (case $Type
      (
        (FHyp (match-atom $Data (Typecode $t) (match-atom $Data (FVar $v) (add-atom &stack ((Num $stack_len) ($t $v)))))) 
        (EHyp (match-atom $Data (Statement $s) (add-atom &stack ((Num $stack_len}) $s))))
      )) 
    (Error (label $label) "The label is the label of a nonactive hypothesis.")))

(= (treat_step $label) 
    (let*
      (
        (() (println! (»»» treating label $label)))
        (($Type $Data) (unify &frames ((Label $label) $Type $Data) ($Type $Data) (Error (label $label) "No statement  information found for label")))
        ($stack_len (case (collapse (match &stack ( (Num $n) $s ) $n)) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) ))) ;; Stack length is used in all cases.
        (() (println! ($label data: $Data)))
      )
      (case $Type
        (
          (FHyp (treat_hypothesis $label $Type $Data $stack_len)) 
          (EHyp (treat_hypothesis $label $Type $Data $stack_len)) 
          (Assertion (treat_assertion $label $Data $stack_len))
          (Proof (treat_assertion $label $Data $stack_len))
        ))
      ))

(= (treat_normal_proof $proof)
    (let*
      (
        (() (println! (Got Proof: $proof)))
        (() (empty-space &stack)) ;; stack: list[Stmmt] = []
        (() (println! "tnm 2"))
        ;; active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        (() (umatch &frames ((Label $label) FHyp $Data) (add-atom &frames (ActiveHyp $label))))
        (() (println! "tnm 3"))
        (() (umatch &frames ((Label $label) EHyp $Data) (add-atom &frames (ActiveHyp $label))))
        (() (println! "tnm 4"))
        ($_empty_return_values (map-atom $proof $label (treat_step (parse $label))))
      )
      (remove-pattern &frames (ActiveHyp $_))))

(= (verify $proof $conclusion)
    (let*
      (
        (() (println! (Verifying conclusion $conclusion of proof $proof)))
        ($_empty_return_values (treat_normal_proof $proof))
        ($stack_expr (collapse (match &stack ( (Num  $n) $f) $f)))
        (() (if (== () $stack_expr) (Error (assertion: $conclusion) "Empty stack at end of proof.") ()))  
        (() (if (> (size-atom $stack_expr) 1) (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack has more than one entry at end of proof.") ()))
        ($stack_top (car-atom $stack_expr))
        (() (println! (Comparing: $stack_top "==" $conclusion)))
        (() (if (== $conclusion $stack_top) () (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack entry does not match proved assertion.")))
        ; (() (if (not (== $conclusion (car-atom $stack_expr))) (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack entry does not match proved assertion.") ()))
        (() (println! "Correct proof!"))
        (() (empty-space &stack))
      ) ($stack_top)))
      
