; Test file for assignment helper functions
; Functions: add_mand_var, assign_f_hyp_to_var, assign_f_hyps

; Test helper - wrapper around assertEqual for clearer test syntax
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (test $actual $expected) (assertEqual $actual $expected))

; Helper functions needed
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

; Functions under test
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (add_mand_var $kb $tok)
  (unify $kb (Var $tok $_ (Type "$v"))
    (unify $kb (MandVar $tok) () (add-atom $kb (MandVar $tok))) ()))

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (assign_f_hyp_to_var $kb $f_hyp)
  (let ($typecode $var) $f_hyp
    (unify $kb (MandVar $var)
      (let () (remove-atom $kb (MandVar $var)) True)
      False)))

; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (assign_f_hyps $kb Nil) Nil)
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

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

!(println! "=== Testing Assignment Helper Functions ===")
!(println! "")

!(println! "Test 1: add_mand_var adds variable to MandVar set")
!(bind! &kb1 (new-space))
!(add-atom &kb1 (Var x 0 (Type "$v")))
; Adding a variable that exists adds MandVar entry
!(assertEqual (add_mand_var &kb1 x) ())
; Verify it was added
!(assertEqual (matchc &kb1 (MandVar $v) $v) (x))

!(println! "Test 2: add_mand_var skips non-variables")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Constant c (Type "$c")))
; Adding a constant does nothing (returns ())
!(assertEqual (add_mand_var &kb2 c) ())
; Verify nothing was added
!(assertEqual (matchc &kb2 (MandVar $v) $v) ())

!(println! "Test 3: add_mand_var skips already-added variables")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Var x 0 (Type "$v")))
!(add-atom &kb3 (MandVar x))
; Adding again does nothing (already present)
!(assertEqual (add_mand_var &kb3 x) ())
; Still only one entry
!(assertEqual (matchc &kb3 (MandVar $v) $v) (x))

!(println! "Test 4: assign_f_hyp_to_var assigns and removes MandVar")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (MandVar x))
; Assigning f-hyp to mandatory var returns True and removes it
!(assertEqual (assign_f_hyp_to_var &kb4 (class x)) True)
; Verify it was removed
!(assertEqual (matchc &kb4 (MandVar $v) $v) ())

!(println! "Test 5: assign_f_hyp_to_var returns False for non-mandatory var")
!(bind! &kb5 (new-space))
; No MandVar for y, so returns False
!(assertEqual (assign_f_hyp_to_var &kb5 (wff y)) False)

!(println! "Test 6: assign_f_hyps processes empty list")
!(bind! &kb6 (new-space))
; Empty list returns Nil
!(assertEqual (assign_f_hyps &kb6 Nil) Nil)

!(println! "Test 7: assign_f_hyps filters f-hyps by mandatory vars")
!(bind! &kb7 (new-space))
!(add-atom &kb7 (MandVar x))
!(add-atom &kb7 (MandVar z))
; Only (class x) and (set z) should be kept
!(test (assign_f_hyps &kb7 (Cons (class x) (Cons (wff y) (Cons (set z) Nil))))
       (Cons (class x) (Cons (set z) Nil)))
; Verify MandVars were removed
!(assertEqual (matchc &kb7 (MandVar $v) $v) ())

!(println! "Test 8: assign_f_hyps with no mandatory vars")
!(bind! &kb8 (new-space))
; No mandatory vars, so all f-hyps filtered out
!(assertEqual (assign_f_hyps &kb8 (Cons (class x) (Cons (wff y) Nil))) Nil)

!(println! "Test 9: assign_f_hyps preserves order")
!(bind! &kb9 (new-space))
!(add-atom &kb9 (MandVar a))
!(add-atom &kb9 (MandVar c))
; Should return in same order as input
!(test (assign_f_hyps &kb9 (Cons (class a) (Cons (wff b) (Cons (set c) Nil))))
       (Cons (class a) (Cons (set c) Nil)))

!(println! "")
!(println! "=== All assignment helper tests complete ===")
