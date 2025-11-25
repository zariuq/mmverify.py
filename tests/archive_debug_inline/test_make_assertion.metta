; Test file for make_assertion function
; make_assertion: aggregates assertion data from frame stack
; Returns: ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $stmt))

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

; Helper functions needed
(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr)
         (to-list' (cdr-atom $expr) $tail))))

(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

(= (mappend Nil $list) $list)
(= (mappend (Cons $head $tail) $list)
   (Cons $head (mappend $tail $list)))

(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (let $pattern $head $rewrite)
       (empty))))

(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (match-atom $tail $pattern $rewrite)
       (empty))))

(= (match-atom' $expr $pattern $rewrite)
  (case (match-atom $expr $pattern $rewrite)
    ((Empty ())
     ($q $q))))

(= (match-atom'' $expr $pattern $rewrite $Empty)
  (case (match-atom $expr $pattern $rewrite)
    ((Empty $Empty)
     ($q $q))))

(= (collect_lists_by_depth $unordered_list $current $max $ordered_list)
  (if (> $current $max)
    $ordered_list
    (let $current_list (match-atom'' $unordered_list ($current $list) $list Nil)
      (collect_lists_by_depth $unordered_list (+ 1 $current) $max (mappend $ordered_list $current_list)))))

(= (add_mand_var $kb $tok)
  (unify $kb (Var $tok $_ (Type "$v"))
    (unify $kb (MandVar $tok) () (add-atom $kb (MandVar $tok))) ()))

(= (assign_f_hyps $kb Nil) Nil)
(= (assign_f_hyps $kb (Cons $head $tail))
   (let*
    (
      ($tail-result (assign_f_hyps $kb $tail))
      (($typecode $var) $head)
      ($pred (unify $kb (MandVar $var) True False))
    )
      (if (== $pred True)
        (let () (remove-atom $kb (MandVar $var)) (Cons $head $tail-result))
        $tail-result)))

(= (remove-patternc $space $pattern)
   (collapse (let $pattern (match $space $pattern $pattern) (remove-atom $space $pattern))))

; Function under test
(= (make_assertion $kb $stmt)
  (let*
    (
      ($e_hyps_lists (matchc $kb (EList (FSDepth $level) $elist) ($level $elist)))
      ($e_levels (collapse (match-atom' $e_hyps_lists ($l $_) $l)))
      ($e_max_level (if (== $e_levels (())) 0 (max-atom $e_levels)))
      ($e_hyps_list (collect_lists_by_depth $e_hyps_lists 1 $e_max_level Nil))
      ($e_hyps_toks (from-list (flatten-list $e_hyps_list)))
      ($_0 (map-atom $e_hyps_toks $tok (add_mand_var $kb $tok)))
      ($_1 (map-atom $stmt $tok (add_mand_var $kb $tok)))
      ($mand_vars (matchc $kb (MandVar $var) $var))
      ($dvs (matchc $kb (DVar ($x $y) $_ (Type "$d"))
              (unify $kb (MandVar $x)
                (unify $kb (MandVar $y) ($x $y) ()) ())))
      ($f_hyps_lists (matchc $kb (FList (FSDepth $level) $flist) ($level $flist)))
      ($f_levels (collapse (match-atom' $f_hyps_lists ($l $_) $l)))
      ($f_max_level (if (== $f_levels (())) 0 (max-atom $f_levels)))
      ($f_hyps_list (collect_lists_by_depth $f_hyps_lists 1 $f_max_level Nil))
      ($f_hyps (assign_f_hyps $kb $f_hyps_list))
      ($mand_vars' (matchc $kb (MandVar $var) $var))
      ($_2 (remove-patternc $kb (MandVar $var)))
    ) ( (DVars $dvs) (FHyps (from-list $f_hyps)) (EHyps (from-list $e_hyps_list)) (Statement $stmt) )))

!(println! "=== Testing make_assertion ===")
!(println! "")

!(println! "Test 1: Empty frame stack - statement only")
!(bind! &kb1 (new-space))
; No ELists, FLists, DVars, Vars - just a statement with constants
; Expected: no e_hyps, no f_hyps, no dvs
!(test (make_assertion &kb1 (c1 c2 c3))
       ((DVars ()) (FHyps ()) (EHyps ()) (Statement (c1 c2 c3))))

!(println! "Test 2: Single level with variables but no hypotheses")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var x 1 (Type "$v")))
!(add-atom &kb2 (Var y 1 (Type "$v")))
; Statement uses variables, but no e_hyps or f_hyps defined
; Expected: no e_hyps, no f_hyps, no dvs (vars aren't in mand_vars without e_hyps)
!(test (make_assertion &kb2 (wff x y))
       ((DVars ()) (FHyps ()) (EHyps ()) (Statement (wff x y))))

!(println! "Test 3: Single level with one essential hypothesis")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Var ph 1 (Type "$v")))
!(add-atom &kb3 (EList (FSDepth 1) (Cons (wff ph) Nil)))
; Statement with e_hyp: (wff ph)
; Expected: e_hyps = ((wff ph)) - from-list creates tuple
!(test (make_assertion &kb3 (wff ph))
       ((DVars ()) (FHyps ()) (EHyps ((wff ph))) (Statement (wff ph))))

!(println! "Test 4: Essential hypothesis with floating hypothesis")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var ph 1 (Type "$v")))
!(add-atom &kb4 (EList (FSDepth 1) (Cons (wff ph) Nil)))
!(add-atom &kb4 (FList (FSDepth 1) (Cons (wff ph) Nil)))
; e_hyp makes ph mandatory, f_hyp assigns type to ph
; Expected: f_hyps = ((wff ph)), e_hyps = ((wff ph))
!(test (make_assertion &kb4 (implies ph ph))
       ((DVars ()) (FHyps ((wff ph))) (EHyps ((wff ph))) (Statement (implies ph ph))))

!(println! "Test 5: Multiple variables with DV constraints")
!(bind! &kb5 (new-space))
!(add-atom &kb5 (Var x 1 (Type "$v")))
!(add-atom &kb5 (Var y 1 (Type "$v")))
!(add-atom &kb5 (DVar (x y) 1 (Type "$d")))
!(add-atom &kb5 (EList (FSDepth 1) (Cons (set x) Nil)))
!(add-atom &kb5 (FList (FSDepth 1) (Cons (setvar x) (Cons (setvar y) Nil))))
; Both x and y are mandatory (x from e_hyp, y from statement)
; DV constraint (x y) should be included
!(test (make_assertion &kb5 (eq x y))
       ((DVars ((x y))) (FHyps ((setvar x) (setvar y))) (EHyps ((set x))) (Statement (eq x y))))

!(println! "Test 6: DV filtering - only mandatory vars")
!(bind! &kb6 (new-space))
!(add-atom &kb6 (Var x 1 (Type "$v")))
!(add-atom &kb6 (Var y 1 (Type "$v")))
!(add-atom &kb6 (Var z 1 (Type "$v")))
!(add-atom &kb6 (DVar (x y) 1 (Type "$d")))
!(add-atom &kb6 (DVar (y z) 1 (Type "$d")))
!(add-atom &kb6 (FList (FSDepth 1) (Cons (setvar x) Nil)))
; Only x is mandatory (in statement), so neither DV constraint includes only mandatory vars
; (x y): y not mandatory; (y z): neither mandatory
!(test (make_assertion &kb6 (singleton x))
       ((DVars ()) (FHyps ((setvar x))) (EHyps ()) (Statement (singleton x))))

!(println! "Test 7: Multiple frame levels - depth ordering")
!(bind! &kb7 (new-space))
!(add-atom &kb7 (Var ph 1 (Type "$v")))
!(add-atom &kb7 (Var ps 2 (Type "$v")))
!(add-atom &kb7 (EList (FSDepth 1) (Cons (wff ph) Nil)))
!(add-atom &kb7 (EList (FSDepth 2) (Cons (wff ps) Nil)))
!(add-atom &kb7 (FList (FSDepth 1) (Cons (wff ph) Nil)))
!(add-atom &kb7 (FList (FSDepth 2) (Cons (wff ps) Nil)))
; e_hyps should be ordered by depth: level 1 first, then level 2
!(test (make_assertion &kb7 (and ph ps))
       ((DVars ()) (FHyps ((wff ph) (wff ps))) (EHyps ((wff ph) (wff ps))) (Statement (and ph ps))))

!(println! "Test 8: F-hyp not assigned to non-mandatory var")
!(bind! &kb8 (new-space))
!(add-atom &kb8 (Var x 1 (Type "$v")))
!(add-atom &kb8 (Var y 1 (Type "$v")))
!(add-atom &kb8 (FList (FSDepth 1) (Cons (setvar x) (Cons (setvar y) Nil))))
; Only x is mandatory (in statement), so only (setvar x) in f_hyps
!(test (make_assertion &kb8 (singleton x))
       ((DVars ()) (FHyps ((setvar x))) (EHyps ()) (Statement (singleton x))))

!(println! "")
!(println! "=== All make_assertion tests complete ===")
