;; mmverify-utils_petta.metta - Clean reconstruction
!(import! &self ../../PeTTa/lib/lib_he)
!(import! &self ../../PeTTa/lib/lib_prolog)

;;; Check for --log flag in command line args (verbose logging)
;;; By default, logging is OFF. Use --log to enable verbose output.
(= (has-log-flag $args)
   (if (== (size-atom $args) 0)
       false
       (let ($first $rest) (decons-atom $args)
         (if (== $first --log)
             true
             (has-log-flag $rest)))))

;;; Dynamically define printif! based on --log flag
;;; If --log: printif! prints the message
;;; Otherwise: printif! is a no-op (returns true)
!(if (has-log-flag (get_cmdline_args))
    (add-atom &self (= (printif! $msg) (println! $msg)))
    (add-atom &self (= (printif! $msg) true)))

;;; Check for --store-proofs flag in command line args
;;; By default, proof storage is OFF (like mmverify.py). Use --store-proofs to enable storing proofs in &kb.
(= (has-store-proofs-flag $args)
   (if (== (size-atom $args) 0)
       false
       (let ($first $rest) (decons-atom $args)
         (if (== $first --store-proofs)
             true
             (has-store-proofs-flag $rest)))))

;;; Dynamically define maybe-store-theorem! based on --store-proofs flag
;;; If --store-proofs: Store full theorem including ProofSequence
;;; Otherwise: Store theorem without ProofSequence (saves memory, like mmverify.py)
!(if (has-store-proofs-flag (get_cmdline_args))
    (progn
      (add-atom &self (= (maybe-store-theorem! $kb $label $dvs $fhyps $ehyps $s $proof)
                        (add-atom $kb ((Label $label) Theorem ((DVars $dvs) (FHyps $fhyps) (EHyps $ehyps) (Statement $s) (Type "$p") (ProofSequence $proof))))))
      (add-atom &self (= (maybe-store-theorem-incomplete! $kb $label $dvs $fhyps $ehyps $s $proof)
                        (add-atom $kb ((Label $label) Theorem ((DVars $dvs) (FHyps $fhyps) (EHyps $ehyps) (Statement $s) (Type "$p") (ProofSequence $proof) (Incomplete True)))))))
    (progn
      (add-atom &self (= (maybe-store-theorem! $kb $label $dvs $fhyps $ehyps $s $proof)
                        (add-atom $kb ((Label $label) Theorem ((DVars $dvs) (FHyps $fhyps) (EHyps $ehyps) (Statement $s) (Type "$p"))))))
      (add-atom &self (= (maybe-store-theorem-incomplete! $kb $label $dvs $fhyps $ehyps $s $proof)
                        (add-atom $kb ((Label $label) Theorem ((DVars $dvs) (FHyps $fhyps) (EHyps $ehyps) (Statement $s) (Type "$p") (Incomplete True))))))))

;; exec - wrapper for fail-fast execution with error handling
;; Halts execution on Error, returns the evaluated value otherwise
(: exec (-> Atom %Undefined%))
(= (exec $prog)
  (case (catch (eval $prog))
    (((Error $type $context)
        (let true (println! ("ERROR:" (Error $type $context))) 
          (callPredicate halt)))
     ($Else $Else))))

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

;; empty-space - remove all atoms from a space
;; CRITICAL: DO NOT COMMENT OUT - causes stack accumulation bug!
;; See test_stack_cleanup_petta.metta for regression test
(= (empty-space $space)
   (matchc $space $atom (remove-atom $space $atom)))

;; Broken version for testing (stack not cleaned):
;; (= (empty-space $space) ())

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

;; push-frame / pop-frame - return () for clean output
(= (push-frame $fd)
  (let $_ (adjust-state-additive $fd 1) ()))

(= (pop-frame $kb $fd)
  (let $level (get-state $fd)
    (let* (
      (true (printif! (pop-from-level: $level)))
      ($_1 (remove-patternc $kb (EList (FSDepth $level) $elist)))
      ($_2 (remove-patternc $kb (FList (FSDepth $level) $flist)))
      ($_3 (remove-patternc $kb ($1 $2 (FSDepth $level) $Data)))
      ($_4 (adjust-state-additive $fd -1))
    ) ())))

;; add_c - returns () on success, Error on failure
(= (add_c $kb $tok)
  (unify $kb (Constant $tok (Type "$c")) (Error (Constant $tok) "Constant already declared.")
    (unify $kb (Var $tok $_ (Type "$v")) (Error (Var $tok) "Trying to declare as a constant an active variable.")
      (let $_ (add-atom $kb (Constant $tok (Type "$c"))) ()))))

;; add_v - returns () on success, Error on failure
(= (add_v $kb $tok $level)
  (unify $kb (Var $tok $_ (Type "$v")) (Error (Var $tok) "Var already declared and active.")
    (unify $kb (Constant $tok (Type "$c")) (Error (Constant $tok) "Var already declared as constant.")
      (let $_ (add-atom $kb (Var $tok (FSDepth $level) (Type "$v"))) ()))))

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
      (unify $kb (DVar ($ox $oy) (FSDepth $level) (Type "$d"))
        ()
        (add-atom $kb (DVar ($ox $oy) (FSDepth $level) (Type "$d")))))))

; Look up disjoint variables (which are oriented)
(= (lookup_d $kb $x $y) (let ($x' $y') (orient_pair $x $y) (unify $kb (DVar ($x' $y') $_ (Type "$d")) True False)))

;; add_d - tail-recursive DV pair processing (was quadratic with map-atom)
;; Outer loop: iterate over varlist for x
;; Inner loop: for each x, iterate over varlist for y
;; Uses collapse per iteration to force deterministic execution
(= (add_d $kb $varlist $level)
   (add_d_outer $kb $varlist $varlist $level))

;; Outer loop: base case
(= (add_d_outer $kb () $varlist $level)
   ())

;; Outer loop: process one x, recurse
(= (add_d_outer $kb $xs $varlist $level)
   (let ($x $rest_x) (decons-atom $xs)
     (let $_ (collapse (add_d_inner $kb $x $varlist $level))
       (add_d_outer $kb $rest_x $varlist $level))))  ;; tail call

;; Inner loop: base case
(= (add_d_inner $kb $x () $level)
   ())

;; Inner loop: process one (x,y) pair, recurse
(= (add_d_inner $kb $x $ys $level)
   (let ($y $rest_y) (decons-atom $ys)
     (let $_ (add_dv_pair_if_fresh $kb $x $y $level)
       (add_d_inner $kb $x $rest_y $level))))  ;; tail call

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
                   (let $_ (add-atom $kb ((Label $label) FHyp (FSDepth $level) ((Typecode $typecode) (FVar $var) (Type "$f")))) ()))))))
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
      (let $_ (add-atom $kb ((Label $label) EHyp (FSDepth $level) ((Statement $stmt) (Type "$e")))) ())))

;; collect_lists_by_depth - collect lists from unordered data by depth level
(= (collect_lists_by_depth $unordered_list $current $max $ordered_list)
  (if (> $current $max)
    $ordered_list
    (let $current_list (match-atom'' $unordered_list ($current $list) $list Nil)
      (collect_lists_by_depth $unordered_list (+ 1 $current) $max (mappend $ordered_list $current_list)))))

;; process_mand_vars - tail-recursive processing of mandatory variable tokens
;; Processes each token with collapse to force deterministic execution
(= (process_mand_vars $kb $tokens)
   (process_mand_vars_tail $kb $tokens))

;; Base case: empty token list
(= (process_mand_vars_tail $kb ())
   ())

;; Recursive case: process one token, recurse on rest
(= (process_mand_vars_tail $kb $tokens)
   (let ($tok $rest) (decons-atom $tokens)
     (progn
       (collapse (add_mand_var $kb $tok))
       (process_mand_vars_tail $kb $rest))))  ;; tail call

;; add_mand_var - add mandatory variable marker (new-space version)
;; Uses if-guards to avoid nested case non-determinism
(= (add_mand_var $kb $tok)
  (let $is_var (collapse (match $kb (Var $tok $_ (Type "$v")) found))
    (if (== $is_var ())
        ()  ; not a var, do nothing
        (let $already (collapse (match $kb (MandVar $tok) found))
          (if (== $already ())
              (let $_ (add-atom $kb (MandVar $tok)) ())  ; add and return ()
              ())))))

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
;; add_a - returns () on success
(= (add_a $kb $label $stmt)
  (let ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s)) (make_assertion $kb $stmt)
    (let $_ (add-atom $kb ((Label $label) Assertion ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s) (Type "$a")))) ())))

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
      ;; Use tail-recursive processing to avoid building intermediate results tuple
      ($e_hyps_toks (from-list (flatten-list $e_hyps_list)))
      ($_1 (process_mand_vars $kb $e_hyps_toks))
      ($_2 (process_mand_vars $kb $stmt))
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
            (true (add-atom $subst ($var $entry1:)))
            ($_2 (adjust-state-additive $sp 1))
            ; (true (println! ("added to subst:" $entry1:)))
          ) ($var $entry1:))
        (Error ((sp $sp_val) (entry $entry) (typecode $typecode) (var $var)) "Proof stack entry does not match floating hypothesis."))))

;; apply_subst_tok - apply substitution to single token
(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

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

;; Find all tokens in a statement that are variables
(= (find_vars $kb $stmt)
  (filter-atom $stmt $tok (unify $kb (Var $tok $_ (Type "$v")) True False)))

;; dv_check - check that two variables from different substitutions satisfy DV constraint
;; For $d x y, we need every var in subst(x) to be declared $d with every var in subst(y)
;; Returns true on success, (Error ...) on failure
(= (dv_check $kb $x $y)
  (if (== $x $y)
      (Error ($x $y) "Disjoint variable violation - same variable.")
      (if (lookup_d $kb $x $y)
          true
          (Error ($x $y) "Disjoint variable violation - not declared."))))

;; Check all pairs from x_vars × y_vars
;; Returns true if all pass, or (Error ...) on first failure
;; Uses collapse to make deterministic - collects all results and checks for errors
(= (check_dv_pairs $kb $x_vars $y_vars)
  (let $results (collapse
                  (let $x (superpose $x_vars)
                    (let $y (superpose $y_vars)
                      (dv_check $kb $x $y))))
    ; Find first error in results using expression list format
    (check_dv_results $results)))

;; Helper to find first Error in expression list (not Cons/Nil)
;; Expression list is like (true true true) or ((Error x y) true true)
(= (check_dv_results $results)
  (if (== $results ())
      true  ; empty list = all passed
      (let ($head $tail) (decons-atom $results)
        (case $head
          (((Error $info $msg) (Error $info $msg))  ; found error, return it
           ($_ (check_dv_results $tail)))))))

;; Check DV constraints in a list
;; Uses collapse to make deterministic - collect all results and find first error
;; Single clause with guard handles both empty and non-empty cases
(= (check_dvs $kb $subst $dvs0)
  (if (== $dvs0 ())
      true  ; empty list = no constraints to check
      (let $results (collapse
                      (let $d (superpose $dvs0)
                        (let* (
                          (($d1 $d2) $d)
                          ($x_vars (match $subst ($d1 $sub1) (find_vars $kb $sub1)))
                          ($y_vars (match $subst ($d2 $sub2) (find_vars $kb $sub2)))
                        ) (check_dv_pairs $kb $x_vars $y_vars))))
        (check_dv_results $results))))


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
        ($stack_contents (collapse (match $stack ((Num $n) $s) ($n $s))))
        ;; DEBUG: Uncomment to debug assertion processing
        ;; (true (println! (DEBUG treat_assertion label: $label stack_len: $stack_len npop: $npop sp_val: $sp_val)))
        ;; (true (println! (DEBUG stack contents: $stack_contents)))
        ;; (true (println! (DEBUG fhyps: $fhyps ehyps: $ehyps)))
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
                                 ($_cleanup (delete-space $subst))
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
;; Returns (Error ...) on error, () on success, (incomplete) for ? step
(= (treat_step $kb $stack $sp $label)
    ;; Handle ? (unknown/incomplete step) - per Metamath spec, accept with warning
    ;; Check both symbol ? and string "?" since Prolog->MeTTa conversion may vary
    (if (or (== $label ?) (== $label "?"))
        (progn
          (println! "WARNING: ? (unknown step) in proof - marking as incomplete")
          (incomplete))
        (let*
          (
            (true (printif! (»»» treating label $label)))
            (($Type $Data)
               (case (collapse (match $kb ((Label $label) $Type $Data) ($Type $Data)))
                 (((($t $d)) ($t $d))
                  (()
                    (case (collapse (match $kb ((Label $label) $Type (FSDepth $level) $Data) ($Type $Data)))
                      (((($t $d)) ($t $d))
                       (() (Error (label $label) "No statement information found for label"))))))))
            ($stack_len (case (collapse (match $stack ((Num $n) $s) $n)) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) )))
            (true (printif! ($Type $label data: $Data)))
          )
          (let $result
            (case $Type
              (
                (FHyp (treat_hypothesis $kb $stack $label $Type $Data $stack_len))
                (EHyp (treat_hypothesis $kb $stack $label $Type $Data $stack_len))
                (Assertion (treat_assertion $kb $stack $sp $label $Data $stack_len))
                (Theorem (treat_assertion $kb $stack $sp $label $Data $stack_len))
              ))
            (let true (printif! (stack ($label): (collapse (match $stack $s $s))))
              $result)))))

;; treat_step_with_errors - treat step and record errors/incomplete markers in error space
(= (treat_step_with_errors $kb $stack $sp $errors $label)
    (let $result (treat_step $kb $stack $sp $label)
      (case $result
        (((Error $info $msg)
           (add-atom $errors (Error $info $msg)))
         ((incomplete)
           (add-atom $errors (incomplete)))
         ($_ ())))))

;; process_proof_steps - tail-recursive proof step processing
;; Processes each step with collapse to force deterministic execution
;; Errors are recorded in $errors space as side effects
(= (process_proof_steps $kb $stack $sp $errors $proof)
   (process_proof_steps_tail $kb $stack $sp $errors $proof))

;; Base case: empty proof
(= (process_proof_steps_tail $kb $stack $sp $errors ())
   ())

;; Recursive case: process one step, recurse on rest
(= (process_proof_steps_tail $kb $stack $sp $errors $proof)
   (let ($label $rest) (decons-atom $proof)
     (progn
       (collapse (treat_step_with_errors $kb $stack $sp $errors $label))
       (process_proof_steps_tail $kb $stack $sp $errors $rest))))  ;; tail call

;; treat_normal_proof - process a proof sequence (new-space version)
;; Returns first (Error ...) if any step fails, (incomplete) if ? found, () on success
(= (treat_normal_proof $kb $stack $sp $proof)
    (let $errors (new-space)
      (let*
        (
          (true (printif! (Got Proof: $proof)))
          ($_1 (empty-space $stack))
          ($_2 (collapse (match $kb ((Label $label) FHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
          ($_3 (collapse (match $kb ((Label $label) EHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
          ($_4 (process_proof_steps $kb $stack $sp $errors $proof))
          ($_5 (remove-patternc $kb (ActiveHyp $_)))
          ;; Query errors space directly instead of using filter-atom
          ($real_errors (collapse (match $errors (Error $i $m) (Error $i $m))))
          ($incomplete_markers (collapse (match $errors (incomplete) (incomplete))))
          ($_cleanup (delete-space $errors))
        )
        ;; Return first real error if any, else (incomplete) if present, else ()
        (if (> (size-atom $real_errors) 0)
            (car-atom $real_errors)
            (if (> (size-atom $incomplete_markers) 0) (incomplete) ())))))

;; ============ Compressed Proof Support ============

;; get-mand-hyp-labels - get mandatory hypotheses for a statement
;; Returns list of labels for f-hyps in the right order
(= (get-mand-hyp-labels $kb $stmt)
   (let*
     (
       ;; Collect all f-hyps with their frame depth from all levels
       ($f_hyps_lists (collapse (match $kb (FList (FSDepth $level) $flist) ($level $flist))))
       ($f_levels (collapse (match-atom' $f_hyps_lists ($l $_) $l)))
       ($f_max_level (if (== $f_levels (())) 0 (max-atom $f_levels)))
       ($f_hyps_list (collect_lists_by_depth $f_hyps_lists 1 $f_max_level Nil))
       ;; Find which variables are in the statement
       ($stmt_vars (find_vars $kb $stmt))
     )
     ;; Filter f-hyps to those whose variable is in the statement, get labels
     (get-fhyp-labels-for-vars $kb $f_hyps_list $stmt_vars)))

;; var-in-list - check if variable is in list
(= (var-in-list $v ()) False)
(= (var-in-list $v $vars)
   (let ($head $tail) (decons-atom $vars)
     (if (== $v $head)
         True
         (var-in-list $v $tail))))

;; get-fhyp-labels-for-vars - get labels of f-hyps for given variables
(= (get-fhyp-labels-for-vars $kb Nil $vars) ())
(= (get-fhyp-labels-for-vars $kb (Cons ($tc $var) $rest) $vars)
   (let $rest_labels (get-fhyp-labels-for-vars $kb $rest $vars)
     (if (var-in-list $var $vars)
         ;; Variable is in vars - find its label
         (let $label_result (collapse (match $kb ((Label $l) FHyp $_ ((Typecode $tc) (FVar $var) (Type "$f"))) $l))
           (if (== $label_result ())
               $rest_labels  ; no label found, skip
               (cons-atom (car-atom $label_result) $rest_labels)))
         $rest_labels)))  ; variable not in stmt, skip

;; get-mand-ehyp-stmts - get ALL essential hypothesis STATEMENTS from ALL frames in scope
;; For compressed proofs, we need the actual e-hyp statements to find their variables
;; Returns list of e-hyp statements in frame order (level 1 first, then level 2, etc.)
(= (get-mand-ehyp-stmts $kb)
   (let*
     (
       ;; Collect all e-hyps with their frame depth from all levels
       ($e_hyps_lists (collapse (match $kb (EList (FSDepth $level) $elist) ($level $elist))))
       ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
       ($e_max_level (if (== $e_levels (())) 0 (max-atom $e_levels)))
     )
     ;; Return the e-hyp statements directly (they're already in $e_hyps_lists)
     (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil)))

;; find-vars-in-stmts - find all variables that appear in a list of statements
(= (find-vars-in-stmts $kb Nil $acc) $acc)
(= (find-vars-in-stmts $kb (Cons $stmt $rest) $acc)
   (let $stmt_vars (find_vars $kb $stmt)
     (find-vars-in-stmts $kb $rest (merge-vars $acc $stmt_vars))))

;; merge-vars - merge two variable lists, removing duplicates
;; BUGFIX: Use single clause with if/case to prevent multiple clause matches causing non-determinism
(= (merge-vars $vars1 $vars2)
   (if (== $vars1 ())
       $vars2  ; First empty, return second (even if also empty)
       (if (== $vars2 ())
           $vars1  ; Second empty (and first not empty)
           (let ($h $t) (decons-atom $vars1)
             (if (var-in-list $h $vars2)
                 (merge-vars $t $vars2)  ; already in vars2, skip
                 (cons-atom $h (merge-vars $t $vars2)))))))  ; add to result

;; get-mand-ehyp-labels - get ALL essential hypothesis labels from ALL frames in scope
;; For compressed proofs, ALL e-hyps in scope are included (not filtered by statement variables)
;; Returns list of e-hyp labels in frame order (level 1 first, then level 2, etc.)
(= (get-mand-ehyp-labels $kb)
   (let*
     (
       ;; Collect all e-hyps with their frame depth from all levels
       ($e_hyps_lists (collapse (match $kb (EList (FSDepth $level) $elist) ($level $elist))))
       ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
       ($e_max_level (if (== $e_levels (())) 0 (max-atom $e_levels)))
       ($e_hyps_list (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil))
     )
     ;; Get labels for all e-hyps (each e-hyp is a statement in a list)
     (get-ehyp-labels-for-stmts $kb $e_hyps_list)))

;; get-ehyp-labels-for-stmts - get labels for e-hyps given their statements
(= (get-ehyp-labels-for-stmts $kb Nil) ())
(= (get-ehyp-labels-for-stmts $kb (Cons $stmt $rest))
   (let $rest_labels (get-ehyp-labels-for-stmts $kb $rest)
     ;; Find label for this e-hyp statement
     (let $label_result (collapse (match $kb ((Label $l) EHyp $_ ((Statement $stmt) (Type "$e"))) $l))
       (if (== $label_result ())
           $rest_labels  ; no label found, skip
           (cons-atom (car-atom $label_result) $rest_labels)))))

;; append-element - append a single element to an expression (NOT prepend!)
;; Used for saved list in compressed proofs where order matters
;; Python: saved_stmts.append(stmt) - we need same behavior
(= (append-element $expr $elem)
   (from-list (mappend (to-list $expr) (Cons $elem Nil))))

;; expand-compressed-step - expand a single compressed step
;; Takes: index, mandatory hyp labels, explicit labels, saved proofs
;; Returns: (label saved_proofs) or (save saved_proofs) or (Error ...)
;; Handles both old format (-1 for save, "?" for incomplete) and new DAG format (save/incomplete atoms)
(= (expand-compressed-step $idx $mand_hyps $labels $saved $num_mand $num_labels)
   (if (or (== $idx -1) (== $idx save))
       ;; Z marker (save current stack top) - both -1 (old) and save atom (DAG)
       (save $saved)
       (if (or (== $idx "?") (== $idx ?) (== $idx incomplete))
           ;; Incomplete proof marker - "?" / ? (old) or incomplete atom (DAG)
           (incomplete-marker $saved)
           (let $num_total (+ $num_mand $num_labels)
             (if (< $idx $num_mand)
                 ;; Index into mandatory hyps
                 (let $label (index-atom $mand_hyps $idx)
                   ($label $saved))
                 (if (< $idx $num_total)
                     ;; Index into explicit labels
                     (let $label_idx (- $idx $num_mand)
                       (let $label (index-atom $labels $label_idx)
                         ($label $saved)))
                     ;; Reference to saved proof - push the saved statement
                     (let $save_idx (- $idx $num_total)
                       (if (>= $save_idx (size-atom $saved))
                           (Error ((idx $idx) (save_idx $save_idx) (saved_len (size-atom $saved))) "Compressed proof save index out of bounds")
                           (let $saved_stmt (index-atom $saved $save_idx)
                             ((push-saved $saved_stmt) $saved))))))))))

;; treat_compressed_proof - process a compressed proof
;; Returns () on success, (Error ...) on failure, (incomplete) if ? found
(= (treat_compressed_proof $kb $stack $sp $labels $steps $stmt)
   (let $errors (new-space)
     (let*
       (
         (true (printif! (Got Compressed Proof: labels $labels steps $steps)))
         ($_1 (empty-space $stack))
         ($_2 (collapse (match $kb ((Label $label) FHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
         ($_3 (collapse (match $kb ((Label $label) EHyp $FSDepth $Data) (add-atom $kb (ActiveHyp $label)))))
         ;; BUGFIX: Get mandatory hyps from active frame, NOT from calling theorem's statement
         ;; Mandatory hyps are ALL active f-hyps + ALL active e-hyps (in order)
         ;; This matches the Metamath spec and other verifiers (metamath.exe, knife)
         ;; Get f-hyps list (all active f-hyps with typecode and var)
         ($f_hyps_lists (collapse (match $kb (FList (FSDepth $level) $flist) ($level $flist))))
         ($f_levels (collapse (match-atom' $f_hyps_lists ($l $_) $l)))
         ($f_max_level (if (== $f_levels (())) 0 (max-atom $f_levels)))
         ($f_hyps_list (collect_lists_by_depth $f_hyps_lists 1 $f_max_level Nil))
         ;; Get e-hyp statements to find their variables
         ($ehyp_stmts (get-mand-ehyp-stmts $kb))
         ;; Find all variables in e-hyps
         ($ehyp_vars (find-vars-in-stmts $kb $ehyp_stmts ()))
         ;; Find variables in conclusion
         ($stmt_vars (find_vars $kb $stmt))
         ;; Merge to get all needed variables (fixes both original bug and idi bug)
         ($all_vars (merge-vars $ehyp_vars $stmt_vars))
         ;; Get f-hyp labels for those variables only
         ($fhyp_labels (get-fhyp-labels-for-vars $kb $f_hyps_list $all_vars))
         (true (printif! (DEBUG fhyp_labels: $fhyp_labels)))
         ($ehyp_labels (get-mand-ehyp-labels $kb))
         (true (printif! (DEBUG ehyp_labels: $ehyp_labels)))
         ;; Concatenate f-hyp labels + e-hyp labels (order matters!)
         ;; Both return expression format (a b c ...), use from-list + mappend + to-list
         ($mand_hyps (from-list (mappend (to-list $fhyp_labels) (to-list $ehyp_labels))))
         ($num_mand (size-atom $mand_hyps))
         ($num_labels (size-atom $labels))
         ;; DEBUG: uncomment to debug mandatory hypothesis computation
         ;; (true (println! (DEBUG syl: fhyp_labels: $fhyp_labels)))
         ;; (true (println! (DEBUG syl: ehyp_labels: $ehyp_labels)))
         ;; (true (println! (DEBUG syl: mand_hyps: $mand_hyps num: $num_mand)))
         ;; (true (println! (DEBUG syl: labels: $labels num: $num_labels)))
         ;; Process each step
         ($_4 (process-compressed-steps $kb $stack $sp $errors $steps $mand_hyps $labels () $num_mand $num_labels))
         ($_5 (remove-patternc $kb (ActiveHyp $_)))
         ($real_errors (collapse (match $errors (Error $i $m) (Error $i $m))))
         ($incomplete_markers (collapse (match $errors (incomplete) (incomplete))))
         ($_cleanup (delete-space $errors))
       )
       (if (> (size-atom $real_errors) 0)
           (car-atom $real_errors)
           (if (> (size-atom $incomplete_markers) 0) (incomplete) ())))))

;; process-compressed-steps - process compressed proof steps iteratively
(= (process-compressed-steps $kb $stack $sp $errors () $mand $labels $saved $nm $nl) ())
(= (process-compressed-steps $kb $stack $sp $errors $steps $mand $labels $saved $nm $nl)
   (let ($idx $rest) (decons-atom $steps)
     (let $expanded (expand-compressed-step $idx $mand $labels $saved $nm $nl)
       (case $expanded
         (((Error $i $m) (add-atom $errors (Error $i $m)))
          ((save $saved2)
            ;; Z: save current stack top (highest indexed element)
            (let $stack_items (collapse (match $stack ((Num $n) $f) ($n $f)))
              (if (== $stack_items ())
                  (add-atom $errors (Error (Z-save) "Cannot save: empty stack"))
                  ;; Find the maximum index and get that element
                  (let $max_idx (max-atom (collapse (match-atom' $stack_items ($i $_) $i)))
                    (let $top_stmt (collapse (match-atom' $stack_items ($max_idx $s) $s))
                      ;; CRITICAL: Python appends to saved list, we must do the same!
                      ;; Using cons-atom would prepend, breaking index-atom access
                      (let $new_saved (append-element $saved (car-atom $top_stmt))
                        (process-compressed-steps $kb $stack $sp $errors $rest $mand $labels $new_saved $nm $nl)))))))
          ((incomplete-marker $saved2)
            ;; ? mark - incomplete proof
            (progn
              (add-atom $errors (incomplete))
              (process-compressed-steps $kb $stack $sp $errors $rest $mand $labels $saved2 $nm $nl)))
          (((push-saved $stmt) $saved2)
            ;; Push saved statement onto stack - treat as a hypothesis-free axiom (like Python)
            ;; In Python: treat_step(('$a', (set(), [], [], stmt)), stack)
            ;; This means: an assertion with no dv, no f-hyps, no e-hyps, just the statement
            (let $stack_len (case (collapse (match $stack ((Num $n) $s) $n)) ( ( () 0 ) ( $nums (+ 1 (max-atom $nums))) ))
              (progn
                (add-atom $stack ((Num $stack_len) $stmt))
                (process-compressed-steps $kb $stack $sp $errors $rest $mand $labels $saved2 $nm $nl))))
          (($label $saved2)
            ;; Normal label - treat it
            (progn
              (treat_step_with_errors $kb $stack $sp $errors $label)
              (process-compressed-steps $kb $stack $sp $errors $rest $mand $labels $saved2 $nm $nl))))))))

;; verify - verify proof yields expected conclusion (new-space version)
;; Returns (Error ...) on failure, (incomplete) if ? found, (success $stack_top) on success
;; Handles both normal proofs (list of labels) and compressed proofs (compressed $labels $steps)
(= (verify $kb $stack $sp $proof $conclusion)
   (let $proof_result (verify-dispatch $kb $stack $sp $proof $conclusion)
      (case $proof_result
        (((Error $info $msg)
           (Error $info $msg))
         ((incomplete)
           (incomplete))
         (()
           (let $stack_expr (collapse (match $stack ((Num $n) $f) $f))
             ; Check for empty stack
             (if (== () $stack_expr)
                 (Error (assertion: $conclusion) "Empty stack at end of proof.")
                 ; Check for multiple items on stack
                 (if (> (size-atom $stack_expr) 1)
                     (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack has more than one entry at end of proof.")
                     ; Get stack top and verify it matches conclusion
                     (let $stack_top (car-atom $stack_expr)
                       (let* ((true (printif! (Comparing: $stack_top "==" $conclusion))))
                         (if (== $conclusion $stack_top)
                             (let* ((true (printif! "Correct proof!")))
                               (success $stack_top))
                             (Error ((assertion: $conclusion) (stack: $stack_expr)) "Stack entry does not match proved assertion."))))))))))))

;; verify-dispatch - route to normal or compressed proof handling
;; Check if proof starts with 'compressed' or 'compressed_dag' symbol
(= (verify-dispatch $kb $stack $sp $proof $conclusion)
   (if (== (size-atom $proof) 0)
       (treat_normal_proof $kb $stack $sp $proof)
       (let ($head $rest) (decons-atom $proof)
         (if (== $head compressed)
             ;; Old compressed format: (compressed labels steps)
             (let ($labels $rest2) (decons-atom $rest)
               (let ($steps $_) (decons-atom $rest2)
                 (treat_compressed_proof $kb $stack $sp $labels $steps $conclusion)))
             (if (== $head compressed_dag)
                 ;; New DAG format from Prolog: (compressed_dag labels dag_steps)
                 ;; dag_steps contain: integers, save, incomplete
                 (let ($labels $rest2) (decons-atom $rest)
                   (let ($dag_steps $_) (decons-atom $rest2)
                     (treat_compressed_proof $kb $stack $sp $labels $dag_steps $conclusion)))
                 ;; Normal proof
                 (treat_normal_proof $kb $stack $sp $proof))))))


;; add_p - add a proof to the knowledge base (new-space version)
;; Returns () on success, (Error ...) on failure
;; NOTE: Uses pattern matching dispatch because PeTTa case doesn't reliably match (success $x) patterns
(= (add_p $kb $stack $sp $label $stmt $proof $verify_proofs)
  (progn
    (printif! "")
    (printif! (Verifying conclusion ($label) $stmt with proof $proof))
    (let $verify_result (if $verify_proofs (verify $kb $stack $sp $proof $stmt) (skip-verify))
      (add_p_dispatch $kb $label $stmt $proof $verify_result))))

;; Helper to dispatch based on verify result - uses pattern matching
(= (add_p_dispatch $kb $label $stmt $proof (skip-verify))
   (let $assertion_data (make_assertion $kb $stmt)
     (let ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s)) $assertion_data
       (progn
         (maybe-store-theorem! $kb $label $dvs $f_hyps $e_hyps $s $proof)
         ()))))

(= (add_p_dispatch $kb $label $stmt $proof (Error $info $msg))
   (prog1 (Error $info $msg)
     (println! ("PROOF FAILED:" $label (Error $info $msg)))))

;; Handle incomplete proofs (containing ?) - add with warning, return ()
(= (add_p_dispatch $kb $label $stmt $proof (incomplete))
   (let $assertion_data (make_assertion $kb $stmt)
     (let ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s)) $assertion_data
       (progn
         (println! ("WARNING: Incomplete proof for" $label "- adding as unverified"))
         (maybe-store-theorem-incomplete! $kb $label $dvs $f_hyps $e_hyps $s $proof)
         ()))))

(= (add_p_dispatch $kb $label $stmt $proof (success $stack_top))
   (let $assertion_data (make_assertion $kb $stmt)
     (let ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $s)) $assertion_data
       (progn
         (maybe-store-theorem! $kb $label $dvs $f_hyps $e_hyps $s $proof)
         ()))))

