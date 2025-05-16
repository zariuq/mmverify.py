;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metta definitions helpful in transpiling mmverify.py into MeTTa     ;;
;;                                                                     ;;
;;                                                                     ;;
;;                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Generic Utilities Section

;; Collapse is used to pull-in non-determinism
(: matchc (-> hyperon::space::DynSpace Atom Atom %Undefined%))
(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

;; Ok, ran into an endless memory error due to collapse_empties.  I'm removing it and ematch.  I'll remove these comments after they're logged in a git commit.
; ;; Probably silly, but it looks better to pcollapse (() () () ()) into () to match () in a let* statement.
; (= (collapse_empties $expr)
;   (foldl-atom $expr () $x $acc (if (== $x $acc) () (Error ($x not_equal_to $acc) "I should only receive ()s"))))

; (: ematch (-> hyperon::space::DynSpace Atom Atom %Undefined%))
; (= (ematch $space $pattern $query) (collapse_empties (matchc $space $pattern $query)))

(= (empty-space $space) (matchc $space $atom (remove-atom $space $atom)))

(= (remove-pattern $space $pattern) (matchc $space $pattern (remove-atom $space $pattern)))

;; Unused sequential alternative to the parallel match-statement version
(= (remove_from_stack $stack_ptr $stack_len)
  (if (> $stack_len $stack_ptr)
    (let () (match &stack ( (Num $stack_ptr) $s ) (remove-atom &stack ( (Num $stack_ptr) $s ))) (remove_from_stack (+ 1 $stack_ptr) $stack_len))
    ()))

;; Super-handy function for matching atoms in an expression.
(: match-atom (-> Expression Atom Atom %Undefined$))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (let $pattern $head $rewrite) (empty)))
(= (match-atom $expr $pattern $rewrite)
   (if-decons-expr $expr $head $tail (match-atom $tail $pattern $rewrite) (empty)))

;; I think match-atom was pruning the branch of the let*-statement, thus catching Empty helps.
(: match-atom' (-> Expression Atom Atom %Undefined$))
(= (match-atom' $expr $pattern $rewrite) (case (match-atom $expr $pattern $rewrite) ( (Empty () ) ( $q $q ) )))

; No longer used due to adjust-state-additive
(= (update-atom $space $atom $update_pattern)
  (match $space $atom (let () (add-atom $space $update_pattern) (remove-atom $space $atom))))

(= (adjust-state-additive $state $delta)
   (chain (get-state $state) $current
     (change-state! $state (+ $current $delta))))

;; List Utility Section

;; Declaration of List data type and constructors
; (: List (-> $a Type))
; (: Nil (List $a))
; (: Cons (-> $a (List $a) (List $a)))

;; Convert an expression into a list.
; (: to-list (-> Expression (List Atom)))
(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

; (: to-list' (-> Expression (List Atom) (List Atom)))
(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr)
         (to-list' (cdr-atom $expr) $tail))))

;; Take a list of lists and flatten it.
; (: flatten-list (-> (List Atom) (List Atom)))
(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

;; Convert a list into an expression
; (: from-list (-> (List Atom) Expression))
; (: from-list (-> (List $a) Expression))
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

;; Flatten an expression
; (: flatten-expr (-> Expression Expression))
(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

;; The sacred union of lists - append brings two into one
; (: append (-> (List $a) (List $a) (List $a)))
(= (append Nil $list) $list)
(= (append (Cons $head $tail) $list) 
   (Cons $head (append $tail $list)))

; (: append-expr (-> Expression Expression Expression))
; (= (append-expr $expr1 $expr2)
;    (from-list (append (to-list $expr1) (to-list $expr2))))

;; Data Adding Section

(= (add_c $tok)
  (unify &kb (Constant $tok (Type "$c")) (Error (Constant $tok) "Constant already declared.") 
    (unify &kb (Var $tok $_ (Type "$v")) (Error (Var $tok) "Trying to declare as a constant an active variable.") 
      (add-atom &kb ( Constant $tok (Type "$c") )))))

(= (add_v $tok $level)
  (unify &kb (Var $tok ($_ (Type "$v"))) (Error (Var $tok) "Var already declared and active.")
    (unify &kb (Constant $tok (Type "$c")) (Error (Constant $tok) "Var already declared as constant.")
      (add-atom &kb ( Var $tok (FSDepth $level) (Type "$v") )))))

(= (add_f $label $typecode $var $level)
  (unify &kb (Var $var $_ (Type "$v")) 
    (unify &kb (Constant $typecode (Type "$c")) 
      (unify &kb ( (Label $label') FHyp (FSDepth $FSDepth) ( (Typecode $typecode') (FVar $var) (Type "$f") ) ) 
        (Error ( (Label $label') (Typecode $typecode') (Var $var) ) "Var in $f already typed by an active $f-statement." )
        (let*
          ( 
            ($flist_entry (to-list (($typecode $var))))
            (() (unify &kb (FList $flist) 
              (let $flist' (append $flist $flist_entry) (update-atom &kb (FList $flist) (FList $flist')))  
              (add-atom &kb (FList $flist_entry))))
          )
            (add-atom &kb ( (Label $label) FHyp (FSDepth $level) ( (Typecode $typecode) (FVar $var) (Type "$f") )))
        )
      )
      (Error (Constant $typecode) "Typecode in $f not declared."))
    (Error (Var $var) "Var in $f not declared."))
)

;; Oh, there are no checks.  So this is nearly trivial.  I actually just keep it as is.  But I do both the e_labels (i.e., e with FSDepth, and e.append, i.e., the $EList)
(= (add_e $label $stmt $level)
  (let*
    (
      ($elist_entry (to-list ($stmt)))
      (() (unify &kb (EList $elist)
        (let $elist' (append $elist $elist_entry) (update-atom &kb (EList $elist) (EList $elist')))
        (add-atom &kb (EList $elist_entry))))
    )
      (add-atom &kb ( (Label $label) EHyp (FSDepth $level) ( (Statement {$stmt) (Type "$e") )))
    )

;; Substitution Section

;; Add a substiution to the substitution-space, based on a floating hypothesis.
;; Ensures that the assertion's floating hypotheses match the stack entries.
(= (add-subst $subst ($typecode $var))
  (let*
    (
      ; ($sp (match &wm (sp $sp) $sp))
      ($sp (get-state &sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      (($entry0 $entry1:) (decons-atom $entry))
    ) (if (== $entry0 $typecode)
        (let* 
          (
            (() (println! ("adding subst" $var $entry1:)))
            (() (add-atom $subst ($var $entry1:)))
            ; (() (update-atom &wm (sp $n) (sp (+ $n 1))))
            ($_ (adjust-state-additive &sp 1))
          ) ($var $entry1:))
        (Error ( (sp $sp) (entry $entry) (typecode $typecode) (var $var) ) "Proof stack entry does not match floating hypothesis."))))


;; Apply a substitution from the substitution space to a token
(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

;; Apply a space of substitutions to a statement
(= (apply_subst $subst $stmt)
    (flatten-expr (map-atom $stmt $tok (apply_subst_tok $subst $tok))))

;; Check that the substitutions in the substitution space applied to an essential hypothesis match the appropriate term in the stack.
(= (check_subst $subst $ehyp)
  (let* 
    (
      ; ($sp (match &wm (sp $sp) $sp))
      ($sp (get-state &sp))
      ($entry (match &stack ((Num $sp) $s) $s))
      ($subst_h (apply_subst $subst $ehyp))
    ) (if (== $entry $subst_h)
        ; (update-atom &wm (sp $n) (sp (+ $n 1)))
        (adjust-state-additive &sp 1)
        (Error ( (sp $sp) (entry $entry) (ehyp $ehyp) (subst_h $subst_h) ) "Proof stack entry does not match essential hypothesis."))))

;; Disjoint Variable Check Section

;; Map over the atoms in a pair of lists
(= (map-pairs $list1 $list2 $fn)
   (map-atom $list1 $v1
     (map-atom $list2 $v2
       ($fn $v1 $v2))))

;; Find all tokens in a statement that are variables
(= (find_vars $stmt)
  (filter-atom $stmt $tok (unify &kb (Var $tok $_) True False)))

;; Orient pairs as (min, max)
(= (orient_pair $x $y)
   (((py-atom min) $x $y) ((py-atom max) $x $y))) 

;; Look up disjoint variables (which are oriented)
(= (lookup_d $x $y) (let ($x' $y') (orient_pair $x $y) (unify &kb (DVar ($x' $y') $_) True False)))

;; Check $x and $y, vars in a substitution: if they're the same or not tagged as disjoint, throw an error 
;; (because disjointness must be preserved transively through substitution)
(= (dv_check $x $y)
  (if (or
        (== $x $y)
        (not (lookup_d $x $y)))
      (Error ($x $y) "Disjoint variable violation.")
      ()))

;; Check whether the substitutions satisfy the disjoint variable conditions
(= (check_dvs $subst $dvs0)
    (map-atom $dvs0 $d 
      (let ($d1 $d2) $d ;; the for x, y in dvs0
        (let ($x_vars $y_vars)
          (match $subst ($d1 $sub1) 
            (match $subst ($d2 $sub2) 
              ((find_vars $sub1) (find_vars $sub2)))) 
          (map-pairs $x_vars $y_vars dv_check)))))


;; Proof Verification Section

;; The assertion part of the treat_step function.
;; Calculates the # of atoms to pop from the stack, 
;; Creates a substitution space from the floating hypotheses, ensuring they match the stack entries,
;; Checks that applying these substitutions to the essential hypotheses match the stack entries,
;; Checks that the substitutions satisfy the disjoint variables,
;; Removes used stack entries,
;; Creates a new conclusion by applying the substitutions to the assertion (or proof) statement.
;; Pushes this onto the stack and resets the stack pointer $sp in the working memory space &wm.
(= (treat_assertion $label $Data $stack_len)
    (let*
      (
        ($dvars (match-atom' $Data (DVars $dvars) $dvars ))
        ($fhyps (match-atom' $Data (FHyps $fhyps) $fhyps ))
        ($ehyps (match-atom' $Data (EHyps $ehyps) $ehyps ))
        ($statement (match-atom' $Data (Statement $statement) $statement ))
        ($lf (size-atom $fhyps))
        ($le (size-atom $ehyps))
        ($npop (+ $lf $le))
        ($sp (- $stack_len $npop))
        (() (println! (stack_len: $stack_len , npop: $npop , sp: $sp)))
        (() (if (< $sp 0) (Error ((label $label) (npop $npop)) "Stack underflow: proof step requires too many hypotheses") ()))
        ; (() (add-atom &wm (sp $sp)))
        ($_0 (change-state! &sp $sp))
        ($subst (new-space)) ; ($subst &subst)
        ($_1 (map-atom $fhyps $fhyp (add-subst $subst $fhyp)))
        ($_2 (map-atom $ehyps $ehyp (check_subst $subst $ehyp)))
        ($_3 (check_dvs $subst $dvars)) ;; I don't like this *idc about the return value* part.
        ($_4 (matchc &stack ( (Num $n) $s ) (if (>= $n $sp) (remove-atom &stack ( (Num $n) $s )) ()))) 
        ($new_conclusion (let $new_conclusion (apply_subst $subst $statement) (let () (add-atom &stack ((Num $sp) $new_conclusion)) $new_conclusion)))
        (() (println! (new_conclusion: $new_conclusion)))
        ; ($_5 (empty-space &wm))
      ) (println! (stack ($label): (matchc &stack $s $s)))))

;; The hypothesis part of the treat_step function
;; Simply adds the floating or essential hypothesis to the stack, ensuring they are active hypotheses.
(= (treat_hypothesis $label $Type $Data $stack_len)
  (unify &kb (ActiveHyp $label) 
    (case $Type
      (
        (FHyp (match-atom' $Data (Typecode $t) (match-atom' $Data (FVar $v) (add-atom &stack ((Num $stack_len) ($t $v)))))) 
        (EHyp (match-atom' $Data (Statement $s) (add-atom &stack ((Num $stack_len) $s))))
      )) 
    (Error (label $label) "The label is the label of a nonactive hypothesis.")))

;; Treats the step by label.
;; Finds the data from the &kb space,
;; Calculates the stack length,
;; And calls the appropriate function: treat hypothesis or treat assertion
(= (treat_step $label) 
    (let*
      (
        (() (println! (»»» treating label $label)))
        (($Type $Data) (unify &kb ((Label $label) $Type $Data) ($Type $Data) (Error (label $label) "No statement information found for label")))
        ($stack_len (case (matchc &stack ( (Num $n) $s ) $n) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) ))) ;; Stack length is used in all cases.
        (() (println! ($Type $label data: $Data)))
      )
      (case $Type
        (
          (FHyp (treat_hypothesis $label $Type $Data $stack_len)) 
          (EHyp (treat_hypothesis $label $Type $Data $stack_len)) 
          (Assertion (treat_assertion $label $Data $stack_len))
          (Proof (treat_assertion $label $Data $stack_len))
        ))
      ))

;; Treats a normal proof (e.g., a list of labels).
;; Adds all hypothesis in the &kb space to the active hypotheses set.  (Q: Is this redundant because the data is extracted via the &kb set, so failing to match the label would indicate it is not active?  I don't fully understand the failure mode here.)
;; Calls treat step for each label in the proof.
;; Removes the active hypotheses
(= (treat_normal_proof $proof)
    (let*
      (
        (() (println! (Got Proof: $proof)))
        ($_0 (empty-space &stack)) ;; stack: list[Stmmt] = []
        ;; active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        ($_1 (matchc &kb ((Label $label) FHyp $FSDepth $Data) (add-atom &kb (ActiveHyp $label))))
        ($_2 (matchc &kb ((Label $label) EHyp $FSDepth $Data) (add-atom &kb (ActiveHyp $label))))
        ($_3 (map-atom $proof $label (treat_step $label)))
      )
      (remove-pattern &kb (ActiveHyp $_))))

;; Verifies that a proof of a conclusion holds.
;; Calls treat normal proof on the proof,
;; Checks that the resulting stack contains exactly one element, which is the desired conclusion.
;; Empties the stack and returns the conclusion (which helps for checking the checker).
(= (verify $proof $conclusion)
    (let*
      (
        (() (println! ""))
        (() (println! (Verifying conclusion $conclusion of proof $proof)))
        ($_0 (treat_normal_proof $proof))
        ($stack_expr (matchc &stack ( (Num  $n) $f) $f))
        (() (if (== () $stack_expr) (Error (assertion: $conclusion) "Empty stack at end of proof.") ()))  
        (() (if (> (size-atom $stack_expr) 1) (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack has more than one entry at end of proof.") ()))
        ($stack_top (car-atom $stack_expr))
        (() (println! (Comparing: $stack_top "==" $conclusion)))
        (() (if (== $conclusion $stack_top) () (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack entry does not match proved assertion.")))
        (() (println! "Correct proof!"))
      ) ($stack_top)))
      
