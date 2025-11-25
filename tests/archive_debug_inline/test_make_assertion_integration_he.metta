; Integration tests for make_assertion based on demo0.mm assertions
; These test real-world scenarios from actual Metamath files

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

; Helper functions (minimal set needed)
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

; make_assertion function
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

!(println! "=== Integration Tests for make_assertion (demo0.mm) ===")
!(println! "")

!(println! "Test 1: tze $a term 0 - No hypotheses, no variables")
!(bind! &kb1 (new-space))
; tze is at top level, no f-hyps or e-hyps
; Statement: (term 0)
; Expected: no DVars, no FHyps, no EHyps
!(test (make_assertion &kb1 (term 0))
       ((DVars ()) (FHyps ()) (EHyps ()) (Statement (term 0))))

!(println! "Test 2: Simple statement with two variables - Two f-hyps at level 1")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Var t 1 (Type "$v")))
!(add-atom &kb2 (Var r 1 (Type "$v")))
!(add-atom &kb2 (FList (FSDepth 1) (Cons (term t) (Cons (term r) Nil))))
; Statement uses t and r as direct tokens (not nested)
; Expected: FHyps = ((term t) (term r)), no EHyps, no DVars
!(test (make_assertion &kb2 (plus t r))
       ((DVars ()) (FHyps ((term t) (term r))) (EHyps ()) (Statement (plus t r))))

!(println! "Test 3: weq $a wff t = r - Two f-hyps for term variables")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Var t 1 (Type "$v")))
!(add-atom &kb3 (Var r 1 (Type "$v")))
!(add-atom &kb3 (FList (FSDepth 1) (Cons (term t) (Cons (term r) Nil))))
; Statement: (wff t = r)
; Expected: FHyps = ((term t) (term r))
!(test (make_assertion &kb3 (wff t = r))
       ((DVars ()) (FHyps ((term t) (term r))) (EHyps ()) (Statement (wff t = r))))

!(println! "Test 4: wim $a wff ( P -> Q ) - Two f-hyps for wff variables")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var P 1 (Type "$v")))
!(add-atom &kb4 (Var Q 1 (Type "$v")))
!(add-atom &kb4 (FList (FSDepth 1) (Cons (wff P) (Cons (wff Q) Nil))))
; Statement: (wff ( P -> Q ))
; Expected: FHyps = ((wff P) (wff Q))
!(test (make_assertion &kb4 (wff (P -> Q)))
       ((DVars ()) (FHyps ((wff P) (wff Q))) (EHyps ()) (Statement (wff (P -> Q)))))

!(println! "Test 5: a2 $a |- ( t + 0 ) = t - One f-hyp")
!(bind! &kb5 (new-space))
!(add-atom &kb5 (Var t 1 (Type "$v")))
!(add-atom &kb5 (FList (FSDepth 1) (Cons (term t) Nil)))
; Statement: (|- ( t + 0 ) = t)
; Only t is a variable (0 is constant)
; Expected: FHyps = ((term t))
!(test (make_assertion &kb5 (|- (t + 0) = t))
       ((DVars ()) (FHyps ((term t))) (EHyps ()) (Statement (|- (t + 0) = t))))

!(println! "Test 6: a1 - Three f-hyps for t, r, s")
!(bind! &kb6 (new-space))
!(add-atom &kb6 (Var t 1 (Type "$v")))
!(add-atom &kb6 (Var r 1 (Type "$v")))
!(add-atom &kb6 (Var s 1 (Type "$v")))
!(add-atom &kb6 (FList (FSDepth 1) (Cons (term t) (Cons (term r) (Cons (term s) Nil)))))
; Statement: (|- ( t = r -> ( t = s -> r = s ) ))
; Expected: FHyps = ((term t) (term r) (term s))
!(test (make_assertion &kb6 (|- (t = r -> (t = s -> r = s))))
       ((DVars ()) (FHyps ((term t) (term r) (term s))) (EHyps ()) (Statement (|- (t = r -> (t = s -> r = s))))))

!(println! "Test 7: mp $a |- Q - With e-hyps in nested scope")
!(bind! &kb7 (new-space))
!(add-atom &kb7 (Var P 1 (Type "$v")))
!(add-atom &kb7 (Var Q 1 (Type "$v")))
!(add-atom &kb7 (FList (FSDepth 1) (Cons (wff P) (Cons (wff Q) Nil))))
!(add-atom &kb7 (EList (FSDepth 2) (Cons (|- P) (Cons (|- (P -> Q)) Nil))))
; Statement: (|- Q)
; e_hyps at level 2: (|- P) and (|- ( P -> Q ))
; P and Q are mandatory (from e_hyps and stmt)
; Expected: FHyps = ((wff P) (wff Q)), EHyps = ((|- P) (|- ( P -> Q )))
!(test (make_assertion &kb7 (|- Q))
       ((DVars ()) (FHyps ((wff P) (wff Q))) (EHyps ((|- P) (|- (P -> Q)))) (Statement (|- Q))))

!(println! "Test 8: Assertion with DV constraint")
!(bind! &kb8 (new-space))
!(add-atom &kb8 (Var x 1 (Type "$v")))
!(add-atom &kb8 (Var y 1 (Type "$v")))
!(add-atom &kb8 (DVar (x y) 1 (Type "$d")))
!(add-atom &kb8 (FList (FSDepth 1) (Cons (setvar x) (Cons (setvar y) Nil))))
; Both x and y are mandatory, DV constraint should be included
!(test (make_assertion &kb8 (|- x != y))
       ((DVars ((x y))) (FHyps ((setvar x) (setvar y))) (EHyps ()) (Statement (|- x != y))))

!(println! "")
!(println! "=== All integration tests complete ===")
