;; mmverify-utils_petta_fresh.metta - Clean reconstruction
!(import! &self ../../PeTTa/lib/lib_he)

; Note, nested match statements inside of defined functions don't work with variable binding in PeTTa.
; (= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

;; To make it work, we need to manually put an eval around $query
;; But this is slow, so we should use (collapse (match)) in the expanded form.
(: matchf (-> %Undefined% Expression Expression %Undefined%))
(= (matchf $space $pattern $query)
   (match $space $pattern (eval $query)))

(: matchc (-> %Undefined% Expression Expression %Undefined%))
(= (matchc $space $pattern $query)
   (collapse (matchf $space $pattern $query)))

;; process_fhyps - process floating hypotheses sequentially, stop on first error
;; Returns True on success, (Error ...) on first failure
;; NOTE: Cannot use (empty) because PeTTa non-determinism causes multiple evaluations
(= (process_fhyps $stack $sp $subst $fhyps)
   (if (== (size-atom $fhyps) 0)
       True
       (let ($first $rest) (decons-atom $fhyps)
         (let $result (add-subst $stack $sp $subst $first)
           (case $result
             (((Error $info $msg) (Error $info $msg))
              ($_ (process_fhyps $stack $sp $subst $rest))))))))

;; process_ehyps - process essential hypotheses sequentially, stop on first error
;; Returns True on success, (Error ...) on first failure
;; NOTE: Cannot use (empty) because PeTTa non-determinism causes multiple evaluations
(= (process_ehyps $stack $sp $subst $ehyps)
   (if (== (size-atom $ehyps) 0)
       True
       (let ($first $rest) (decons-atom $ehyps)
         (let $result (check_subst $stack $sp $subst $first)
           (case $result
             (((Error $info $msg) (Error $info $msg))
              ($_ (process_ehyps $stack $sp $subst $rest))))))))

;; Frame Management Section
;; Explicit frame management for elegant bijection
;; TODO: Future work - pass &fd state and use get-state to avoid explicit level params

(= (push-frame $fd)
  (adjust-state-additive $fd 1))

(= (pop-frame $kb $fd)
  (let $level (get-state $fd)
    (let* (
      ($_ (println! (pop-from-level: $level)))
      ($_1 (remove-patternc $kb (EList (FSDepth $level) $elist)))
      ($_2 (remove-patternc $kb (FList (FSDepth $level) $flist)))
      ($_3 (remove-patternc $kb ($1 $2 (FSDepth $level) $Data)))
    ) (adjust-state-additive $fd -1))))

;; add_c
(= (add_c $kb $tok)
  (case (collapse (match $kb (Constant $tok (Type "$c")) found))
    (((found)
       (Error (Constant $tok) "Constant already declared."))
     (()
       (case (collapse (match $kb (Var $tok $_ (Type "$v")) found))
         (((found)
            (Error (Var $tok) "Trying to declare as a constant an active variable."))
          (()
            (add-atom $kb (Constant $tok (Type "$c"))))))))))

;; add_v
(= (add_v $kb $tok $level)
  (case (collapse (match $kb (Var $tok $_ (Type "$v")) found))
    (((found)
       (Error (Var $tok) "Var already declared and active."))
     (()
       (case (collapse (match $kb (Constant $tok (Type "$c")) found))
         (((found)
            (Error (Constant $tok) "Var already declared as constant."))
          (()
            (add-atom $kb (Var $tok (FSDepth $level) (Type "$v"))))))))))

;; String comparison
(= (string< $x $y) (@< $x $y))

(= (orient_pair $x $y)
   (if (string< $x $y)
       ($x $y)
       ($y $x)))

;; add_dv_pair_if_fresh
(= (add_dv_pair_if_fresh $kb $x $y $level)
  (if (== $x $y) ()
    (let ($ox $oy) (orient_pair $x $y)
      (case (collapse (match $kb (DVar ($ox $oy) (FSDepth $level) (Type "$d")) found))
        (((found) ())
         (() (add-atom $kb (DVar ($ox $oy) (FSDepth $level) (Type "$d")))))))))

;; add_d
(= (add_d $kb $varlist $level)
  (map-atom $varlist $x
    (map-atom $varlist $y
      (add_dv_pair_if_fresh $kb $x $y $level))))

;; List Utils
(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr) (to-list (cdr-atom $expr)))))

(= (mappend Nil $list) $list)
(= (mappend (Cons $head $tail) $list)
   (Cons $head (mappend $tail $list)))

;; from-list - convert Cons/Nil back to expression
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

;; flatten-list - flatten nested expression lists
(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

;; to-list' with tail accumulator
(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr)
         (to-list' (cdr-atom $expr) $tail))))

;; flatten-expr - flatten nested expressions
(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

;; match-atom - search for pattern in expression elements
;; NOTE: Uses (eval $rewrite) to make nested match compose properly in PeTTa
;; This is ~10x slower than pure match but necessary for correct nesting
;; Rule 1: Try to match the head
(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (let $pattern $head (eval $rewrite))
       (empty))))

;; Rule 2: Recursively search the tail (both clauses run non-deterministically)
(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (match-atom $tail $pattern $rewrite)
       (empty))))

;; match-atom' catches Empty to avoid pruning branches
(= (match-atom' $expr $pattern $rewrite)
   (case (match-atom $expr $pattern $rewrite) ( (Empty () ) ( $q $q ) )))

;; match-atom'' with custom Empty default
(= (match-atom'' $expr $pattern $rewrite $Empty)
   (case (match-atom $expr $pattern $rewrite) ( (Empty $Empty) ( $q $q ) )))

;; update-atom
(= (update-atom $space $atom $update_pattern)
  (match $space $atom (let $_ (add-atom $space $update_pattern) (remove-atom $space $atom))))

;; add_f
(= (add_f $kb $label $typecode $var $level)
  (case (collapse (match $kb (Var $var $_ (Type "$v")) found))
    (((found)
       (case (collapse (match $kb (Constant $typecode (Type "$c")) found))
         (((found)
            (case (collapse (match $kb ((Label $label') FHyp (FSDepth $FSDepth) ((Typecode $typecode') (FVar $var) (Type "$f"))) found))
              (((found)
                 ;; Extract actual label and typecode from existing FHyp using matchc
                 (let (($existing_label $existing_typecode))
                      (matchc $kb ((Label $l) FHyp $_ ((Typecode $tc) (FVar $var) (Type "$f"))) ($l $tc))
                   (Error ((Label $existing_label) (Typecode $existing_typecode) (Var $var)) "Var in $f already typed by an active $f-statement.")))
               (()
                 (let*
                   (
                     ($flist_entry (to-list (($typecode $var))))
                     ($_1 (case (collapse (match $kb (FList (FSDepth $level) $flist) $flist))
                            ((($flist)
                               (let $flist' (mappend $flist $flist_entry)
                                 (match $kb (FList (FSDepth $level) $flist)
                                   (let $_2 (add-atom $kb (FList (FSDepth $level) $flist'))
                                     (remove-atom $kb (FList (FSDepth $level) $flist))))))
                             (()
                               (add-atom $kb (FList (FSDepth $level) $flist_entry))))))
                   )
                   (add-atom $kb ((Label $label) FHyp (FSDepth $level) ((Typecode $typecode) (FVar $var) (Type "$f")))))))))
          (()
            (Error (Constant $typecode) "Typecode in $f not declared.")))))
     (()
       (Error (Var $var) "Var in $f not declared.")))))

;; add_e - add essential hypothesis
(= (add_e $kb $label $stmt $level)
  (let*
    (
      ($elist_entry (to-list ($stmt)))
      ($_1 (case (collapse (match $kb (EList (FSDepth $level) $elist) $elist))
             ((($elist)
                (let $elist' (mappend $elist $elist_entry)
                  (match $kb (EList (FSDepth $level) $elist)
                    (let $_2 (add-atom $kb (EList (FSDepth $level) $elist'))
                      (remove-atom $kb (EList (FSDepth $level) $elist))))))
              (()
                (add-atom $kb (EList (FSDepth $level) $elist_entry))))))
    )
      (add-atom $kb ((Label $label) EHyp (FSDepth $level) ((Statement $stmt) (Type "$e"))))))

;; collect_lists_by_depth - collect lists from unordered data by depth level
(= (collect_lists_by_depth $unordered_list $current $max $ordered_list)
  (if (> $current $max)
    $ordered_list
    (let $current_list (match-atom'' $unordered_list ($current $list) $list Nil)
      (collect_lists_by_depth $unordered_list (+ 1 $current) $max (mappend $ordered_list $current_list)))))

;; add_mand_var - add mandatory variable marker (new-space version)
(= (add_mand_var $kb $tok)
  (case (collapse (match $kb (Var $tok $_ (Type "$v")) found))
    (((found)
       (case (collapse (match $kb (MandVar $tok) found))
         (((found) ())
          (() (add-atom $kb (MandVar $tok))))))
     (() ()))))

;; assign_f_hyps - filter f-hypotheses by mandatory variables (new-space version)
(= (assign_f_hyps $kb Nil) Nil)
(= (assign_f_hyps $kb (Cons $head $tail))
   (let*
    (
      ($tail-result (assign_f_hyps $kb $tail))
      (($typecode $var) $head)
      ($pred (case (collapse (match $kb (MandVar $var) found))
               (((found) true)
                (() false))))
    )
      (if (== $pred true)
        (let $_1 (remove-atom $kb (MandVar $var)) (Cons $head $tail-result))
        $tail-result)))

;; remove-patternc - remove all atoms matching pattern
(= (remove-patternc $space $pattern)
   (collapse (let $pattern (match $space $pattern $pattern) (remove-atom $space $pattern))))

;; add_a - add assertion to knowledge base (new-space version)
(= (add_a $kb $label $stmt)
  (let ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s)) (make_assertion $kb $stmt)
    (add-atom $kb ((Label $label) Assertion ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s) (Type "$a"))))))

;; make_assertion - build assertion frame from statement (new-space version)
(= (make_assertion $kb $stmt)
  (let*
    (
      ;; Collect e_hyps from all frame levels
      ($e_hyps_lists (collapse (match $kb (EList (FSDepth $level) $elist) ($level $elist))))
      ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
      ($e_max_level (if (== $e_levels (())) 0 (max-atom $e_levels)))
      ($e_hyps_list (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil))
      ;; Build mandatory vars from e_hyps tokens and statement tokens
      ($e_hyps_toks (from-list (flatten-list $e_hyps_list)))
      ($_1 (map-atom $e_hyps_toks $tok (add_mand_var $kb $tok)))
      ($_2 (map-atom $stmt $tok (add_mand_var $kb $tok)))
      ($mand_vars (collapse (match $kb (MandVar $var) $var)))
      ;; Collect disjoint variable pairs where both vars are mandatory
      ($dvs (collapse (match $kb (DVar ($x $y) $_ (Type "$d"))
              (let $x_list (collapse (match $kb (MandVar $x) $x))
                (let $y_list (collapse (match $kb (MandVar $y) $y))
                  (if (and (not (== $x_list ())) (not (== $y_list ())))
                      ($x $y)
                      ()))))))
      ;; Collect f_hyps from all frame levels
      ($f_hyps_lists (collapse (match $kb (FList (FSDepth $level) $flist) ($level $flist))))
      ($f_levels (collapse (match-atom' $f_hyps_lists ($l $_) $l)))
      ($f_max_level (if (== $f_levels (())) 0 (max-atom $f_levels)))
      ($f_hyps_list (collect_lists_by_depth $f_hyps_lists 1 $f_max_level Nil))
      ($f_hyps (assign_f_hyps $kb $f_hyps_list))
      ;; Cleanup mandatory vars
      ($_3 (remove-patternc $kb (MandVar $var)))
    ) ( (DVars $dvs) (FHyps (from-list $f_hyps)) (EHyps (from-list $e_hyps_list)) (Statement $stmt) )))

;; ============ State Operations ============

;; adjust-state-additive - add delta to a state variable
(= (adjust-state-additive $state $delta)
   (chain (get-state $state) $current
     (change-state! $state (+ $current $delta))))

;; ============ Substitution Functions ============

;; add-subst - add substitution from stack entry (new-space version)
(= (add-subst $stack $sp $subst ($typecode $var))
  (let*
    (
      ($sp_val (get-state $sp))
      ($entry (case (collapse (match $stack ((Num $sp_val) $s) $s))
                ((($s) $s)
                 (() (Error (sp $sp_val) "Stack empty or invalid pointer")))))
      (($entry0 $entry1:) (decons-atom $entry))
    ) (if (== $entry0 $typecode)
        (let*
          (
            ($_1 (add-atom $subst ($var $entry1:)))
            ($_2 (adjust-state-additive $sp 1))
          ) ($var $entry1:))
        (Error ((sp $sp_val) (entry $entry) (typecode $typecode) (var $var)) "Proof stack entry does not match floating hypothesis."))))

;; apply_subst_tok - apply substitution to single token
(= (apply_subst_tok $subst $tok)
   (let $res (collapse (match $subst ($tok $sub) $sub))
     (if (== $res ())
         $tok
         (car-atom $res))))

;; apply_subst - apply substitution to statement
(= (apply_subst $subst $stmt)
    (flatten-expr (map-atom $stmt $tok (apply_subst_tok $subst $tok))))

;; check_subst - verify essential hypothesis matches stack with substitution (new-space version)
(= (check_subst $stack $sp $subst $ehyp)
  (let*
    (
      ($sp_val (get-state $sp))
      ($entry (case (collapse (match $stack ((Num $sp_val) $s) $s))
                ((($s) $s)
                 (() (Error (sp $sp_val) "Stack empty or invalid pointer")))))
      ($subst_h (once (apply_subst $subst $ehyp)))
    ) (if (== $entry $subst_h)
        (adjust-state-additive $sp 1)
        (Error ((sp $sp_val) (entry $entry) (ehyp $ehyp) (subst_h $subst_h)) "Proof stack entry does not match essential hypothesis."))))

;; find_vars - find all variables in an expression
;; Uses Cons list iteration to avoid nested match issues in PeTTa
(= (find-vars-cons $kb Nil) Nil)
(= (find-vars-cons $kb (Cons $head $tail))
   (let $rest (find-vars-cons $kb $tail)
     (let $check (collapse (match $kb (Var $head $_ (Type "$v")) found))
       (if (== $check (found))
           (Cons $head $rest)
           $rest))))

(= (find_vars $kb $expr)
  (from-list (find-vars-cons $kb (to-list $expr))))

;; dv_check - check if two variables from substitutions satisfy DV constraints
;; From mmverify.py line 812: if x0 == y0 or not lookup_d(x0, y0): raise error
;; So: ERROR if x == y OR if no DVar(x, y) exists in current scope
;; SUCCESS only if x != y AND DVar(x, y) is declared
;; Returns (Error ...) for violation, or (empty) for success
;; Use (empty) so case+Empty pattern works in PeTTa
(= (dv_check $kb $x $y)
  (if (== $x $y)
    (Error ($x $y) "Disjoint variable violation: same variable in both substitutions")
    (let ($ox $oy) (orient_pair $x $y)
      (case (collapse (match $kb (DVar ($ox $oy) $_ (Type "$d")) found))
        (((found) (empty))
         (() (Error (disjoint ($x $y)) "Disjoint variable constraint not declared")))))))

;; check_dv_pairs - check all pairs from two variable lists
;; Uses superpose so each successful check (empty) disappears, only errors remain
(= (check_dv_pairs $kb $x_vars $y_vars)
  (let $x (superpose $x_vars)
    (let $y (superpose $y_vars)
      (dv_check $kb $x $y))))

;; check_dvs - check all disjoint variable constraints
;; Uses superpose so each successful check (empty) disappears, only errors remain
;; Returns True for empty dvs, (Error ...) or (empty) for non-empty dvs
;; IMPORTANT: Must handle empty dvs0 specially since (superpose ()) fails in PeTTa
(= (check_dvs $kb $subst $dvs0)
  (if (== (size-atom $dvs0) 0)
      True  ; No DV constraints to check - success
      (let ($d1 $d2) (superpose $dvs0)
        (let $x_vars (match $subst ($d1 $sub1) (find_vars $kb $sub1))
          (let $y_vars (match $subst ($d2 $sub2) (find_vars $kb $sub2))
            (check_dv_pairs $kb $x_vars $y_vars))))))

;; NOTE: verify_dvs, has-dv-error, find-error-in-cons removed
;; Now using case (check_dvs ...) + Empty pattern directly in treat_assertion

;; ============ Proof Verification ============

;; treat_assertion - process assertion during proof verification (new-space version)
(= (treat_assertion $kb $stack $sp $label $Data $stack_len)
    (let*
      (
        ($dvars (match-atom' $Data (DVars $dvars) $dvars))
        ($fhyps (match-atom' $Data (FHyps $fhyps) $fhyps))
        ($ehyps (match-atom' $Data (EHyps $ehyps) $ehyps))
        ($statement (match-atom' $Data (Statement $statement) $statement))
        ($lf (size-atom $fhyps))
        ($le (size-atom $ehyps))
        ($npop (+ $lf $le))
        ($sp_val (- $stack_len $npop))
      )
      (if (< $sp_val 0)
          (Error ((label $label) (npop $npop)) "Stack underflow: proof step requires too many hypotheses")
          (let*
            (
              ($_1 (change-state! $sp $sp_val))
              ($subst (new-space))
            )
            ; Process fhyps - check for type mismatch errors
            (case (process_fhyps $stack $sp $subst $fhyps)
              (((Error $i1 $m1) (Error $i1 $m1))
               (True
                 ; Process ehyps - check for essential hypothesis mismatch
                 (case (process_ehyps $stack $sp $subst $ehyps)
                   (((Error $i2 $m2) (Error $i2 $m2))
                    (True
                      ; Check DV constraints - True or (empty) means success
                      (case (check_dvs $kb $subst $dvars)
                          (((Error $info $msg) (Error $info $msg))
                           ($_
                             (let*
                               (
                                 ($_4 (collapse (match $stack ((Num $n) $s) (if (>= $n $sp_val) (remove-atom $stack ((Num $n) $s)) ()))))
                                 ($new_conclusion (let $nc (once (apply_subst $subst $statement))
                                                    (let $_5 (add-atom $stack ((Num $sp_val) $nc)) $nc)))
                               ) ()))))))))))))))

;; treat_hypothesis - process hypothesis during proof verification (new-space version)
;; Pushes FHyp or EHyp onto the stack if the label is an active hypothesis
(= (treat_hypothesis $kb $stack $label $Type $Data $stack_len)
  (case (collapse (match $kb (ActiveHyp $label) found))
    (((found)
       (case $Type
         ((FHyp
            (let* (
              ($typecode (match-atom' $Data (Typecode $t) $t))
              ($var (match-atom' $Data (FVar $v) $v))
            ) (add-atom $stack ((Num $stack_len) ($typecode $var)))))
          (EHyp
            (let $stmt (match-atom' $Data (Statement $s) $s)
              (add-atom $stack ((Num $stack_len) $stmt)))))))
     (() (Error (label $label) "The label is the label of a nonactive hypothesis.")))))

;; treat_step - dispatch proof step to appropriate handler (new-space version)
;; Returns (Error ...) on error, () on success
(= (treat_step $kb $stack $sp $label)
    (let*
      (
        ($_1 (println! (»»» treating label $label)))
        (($Type $Data)
           (case (collapse (match $kb ((Label $label) $Type $Data) ($Type $Data)))
             (((($t $d)) ($t $d))
              (()
                (case (collapse (match $kb ((Label $label) $Type (FSDepth $level) $Data) ($Type $Data)))
                  (((($t $d)) ($t $d))
                   (() (Error (label $label) "No statement information found for label"))))))))
        ($stack_len (case (collapse (match $stack ((Num $n) $s) $n)) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) )))
        ($_2 (println! ($Type $label data: $Data)))
      )
      (let $result
        (case $Type
          (
            (FHyp (treat_hypothesis $kb $stack $label $Type $Data $stack_len))
            (EHyp (treat_hypothesis $kb $stack $label $Type $Data $stack_len))
            (Assertion (treat_assertion $kb $stack $sp $label $Data $stack_len))
            (Proof (treat_assertion $kb $stack $sp $label $Data $stack_len))
          ))
        (let $_3 (println! (stack ($label): (collapse (match $stack $s $s))))
          $result))))

;; treat_step_with_errors - treat step and record errors in error space
(= (treat_step_with_errors $kb $stack $sp $errors $label)
    (let $result (treat_step $kb $stack $sp $label)
      (case $result
        (((Error $info $msg)
           (add-atom $errors (Error $info $msg)))
         ($_ ())))))

;; treat_normal_proof - process a proof sequence (new-space version)
;; Returns first (Error ...) if any step fails, () on success
(= (treat_normal_proof $kb $stack $sp $proof)
    (let $errors (new-space)
      (let*
        (
          ($_0 (println! (Got Proof: $proof)))
          ($_1 (empty-space $stack))
          ($_2 (collapse (match $kb ((Label $label) FHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
          ($_3 (collapse (match $kb ((Label $label) EHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
          ($_4 (map-atom $proof $label (treat_step_with_errors $kb $stack $sp $errors $label)))
          ($_5 (remove-patternc $kb (ActiveHyp $_)))
          ($error_list (collapse (match $errors $e $e)))
        )
        (if (== $error_list ()) () (car-atom $error_list)))))

;; verify - verify proof yields expected conclusion (new-space version)
;; Returns (Error ...) on failure, stack_top on success
(= (verify $kb $stack $sp $proof $conclusion)
    (let $proof_result (treat_normal_proof $kb $stack $sp $proof)
      (case $proof_result
        (((Error $info $msg)
           (Error $info $msg))
         (()
           (let*
             (
               ($stack_expr (collapse (match $stack ((Num $n) $f) $f)))
               ($_1 (if (== () $stack_expr) (Error (assertion: $conclusion) "Empty stack at end of proof.") ()))
               ($_2 (if (> (size-atom $stack_expr) 1) (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack has more than one entry at end of proof.") ()))
               ($stack_top (car-atom $stack_expr))
               ($_3 (println! (Comparing: $stack_top "==" $conclusion)))
               ($_4 (if (== $conclusion $stack_top) () (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack entry does not match proved assertion.")))
               ($_5 (println! "Correct proof!"))
             ) $stack_top))))))

;; add_p - add a proof to the knowledge base (new-space version)
(= (add_p $kb $stack $sp $label $stmt $proof $verify_proofs)
  (let*
    (
      ($_0 (println! ""))
      ($_1 (println! (Verifying conclusion ($label) $stmt with proof $proof)))
      ($verify_result (if $verify_proofs (verify $kb $stack $sp $proof $stmt) ()))
    )
    ; Check if verification produced an error - if so, return it without adding to KB
    (case $verify_result
      (((Error $info $msg)
         (Error $info $msg))
       ($_
         (let*
           (
             ($_2 (println! ("make_assertion" $label - $stmt)))
             (( (DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $stmt) ) (make_assertion $kb $stmt))
             ($_3 (println! ("gathered assertion data:" $dvs $f_hyps $e_hyps $stmt)))
           )
           (let $_4 (add-atom $kb ( (Label $label) Proof ( (DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $stmt) (Type "$p") (ProofSequence $proof) ))) $verify_result)))))))
