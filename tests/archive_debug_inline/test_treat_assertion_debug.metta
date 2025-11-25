; Debug version of test 2

(= (test $actual $expected) (assertEqual $actual $expected))
(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

(= (match-atom $expr $pattern $rewrite)
  (chain (decons-atom $expr) $ht
    (unify ($head $tail) $ht (let $pattern $head $rewrite) (empty))))
(= (match-atom $expr $pattern $rewrite)
  (chain (decons-atom $expr) $ht
    (unify ($head $tail) $ht (match-atom $tail $pattern $rewrite) (empty))))

(= (match-atom' $expr $pattern $rewrite)
  (case (match-atom $expr $pattern $rewrite)
    ((Empty ())
     ($q $q))))

(= (adjust-state-additive $state $delta)
   (chain (get-state $state) $current
     (change-state! $state (+ $current $delta))))

(= (apply_subst_tok $subst $tok)
  (let $res (unify $subst ($tok $sub) $sub $tok) $res))

(= (apply_subst $subst $stmt)
  (if (== $stmt ())
      ()
      (let*
        (
          (($tok0 $tok_tail:) (decons-atom $stmt))
          ($tok0_new (apply_subst_tok $subst $tok0))
          ($tok_tail_new: (apply_subst $subst $tok_tail:))
        ) ($tok0_new $tok_tail_new:))))

(= (add-subst $stack $sp $subst ($typecode $var))
  (let*
    (
      ($sp_val (get-state $sp))
      (() (println! (add-subst at sp_val: $sp_val for $typecode $var)))
      ($entry (match $stack ((Num $sp_val) $s) $s))
      (() (println! (entry: $entry)))
      (($entry0 $entry1:) (decons-atom $entry))
    ) (if (== $entry0 $typecode)
        (let*
          (
            (() (println! (adding subst $var -> $entry1:)))
            (() (add-atom $subst ($var $entry1:)))
            ($_ (adjust-state-additive $sp 1))
          ) ($var $entry1:))
        (Error (entry $entry) (expected (const $typecode)) (var $var)))))

; check_dv_on_subst - simplified for testing
(= (check_dv_on_subst $kb $subst $dv_list)
  Empty)

; treat_assertion implementation
(= (treat_assertion $kb $stack $sp $label $Data $stack_len)
  (let*
    (
      ($dvars (match-atom' $Data (DVars $d) $d))
      ($fhyps (match-atom' $Data (FHyps $f) $f))
      ($ehyps (match-atom' $Data (EHyps $e) $e))
      ($stmt (match-atom' $Data (Statement $s) $s))
      (() (println! (FHyps: $fhyps)))
      (() (println! (Statement: $stmt)))
      ($lf (size-atom $fhyps))
      ($le (size-atom $ehyps))
      (() (println! (lf: $lf le: $le)))
      ($npop (+ $lf $le))
      ($sp_val (- $stack_len $npop))
      (() (println! (stack_len: $stack_len npop: $npop sp_val: $sp_val)))
      (() (if (< $sp_val 0) (Error (label $label) (stack_len $stack_len) (npop $npop) "Stack underflow") ()))
      ; Change stack pointer FIRST
      ($_0 (change-state! $sp $sp_val))
      (() (println! (sp after change: (get-state $sp))))
      ($subst (new-space))
      ; Build substitution from FHyps
      ($_1 (map-atom $fhyps $fh (add-subst $stack $sp $subst $fh)))
      (() (println! (subst: (matchc $subst $s $s))))
      (() (println! (sp after subst: (get-state $sp))))
      ; Check disjoint variables
      ($dv_check (check_dv_on_subst $kb $subst $dvars))
      ; Remove stack entries >= $sp_val
      ($_4 (matchc $stack ((Num $n) $s) (if (>= $n $sp_val) (remove-atom $stack ((Num $n) $s)) ())))
      (() (println! (stack after removal: (matchc $stack $s $s))))
      ; Apply substitution and add to stack
      ($new_conclusion (let $new_conclusion (apply_subst $subst $stmt)
                         (let () (add-atom $stack ((Num $sp_val) $new_conclusion)) $new_conclusion)))
      (() (println! (new_conclusion: $new_conclusion)))
    ) $new_conclusion))

!(println! "=== Debug Test 2: tpl ===")
!(bind! &kb2 (new-space))
!(bind! &stack2 (new-space))
!(bind! &sp2 (new-state 2.0))
!(add-atom &stack2 ((Num 0) ("term" "t")))
!(add-atom &stack2 ((Num 1) ("term" "0")))
!(println! "Initial stack:")
!(println! (matchc &stack2 $s $s))
!(treat_assertion &kb2 &stack2 &sp2 "tpl"
  ((DVars ()) (FHyps (("term" "t") ("term" "r"))) (EHyps ()) (Statement ("term" "(" "t" "+" "r" ")")) (Type "$a")) 2.0)
!(println! "Final stack:")
!(println! (matchc &stack2 $s $s))
!(println! "Final sp:")
!(println! (get-state &sp2))
