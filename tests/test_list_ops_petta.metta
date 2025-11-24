; Test file for list operations (PeTTa version)
; Functions: to-list, to-list', from-list, mappend, flatten-list, flatten-expr

; Import all functions from mmverify-utils_petta.metta
!(import! &self ../mmverify-utils_petta)

!(println! "=== Testing List Operations (PeTTa) ===")
!(println! "")

!(println! "Test 1: to-list converts expression to Cons/Nil")
!(test (to-list (a b c)) (Cons a (Cons b (Cons c Nil))))
!(test (to-list ()) Nil)
!(test (to-list (x)) (Cons x Nil))

!(println! "Test 2: to-list' converts with tail accumulator")
!(test (to-list' (a b) (Cons c Nil)) (Cons a (Cons b (Cons c Nil))))
!(test (to-list' () (Cons x Nil)) (Cons x Nil))

!(println! "Test 3: from-list converts Cons/Nil back to expression")
!(test (from-list (Cons a (Cons b (Cons c Nil)))) (a b c))
!(test (from-list Nil) ())
!(test (from-list (Cons x Nil)) (x))

!(println! "Test 4: to-list and from-list are inverses")
!(test (from-list (to-list (foo bar baz))) (foo bar baz))
!(test (to-list (from-list (Cons 1 (Cons 2 Nil)))) (Cons 1 (Cons 2 Nil)))

!(println! "Test 5: mappend concatenates Cons lists")
!(test (mappend Nil Nil) Nil)
!(test (mappend (Cons a Nil) Nil) (Cons a Nil))
!(test (mappend Nil (Cons b Nil)) (Cons b Nil))
!(test (mappend (Cons a (Cons b Nil)) (Cons c (Cons d Nil)))
       (Cons a (Cons b (Cons c (Cons d Nil)))))

!(println! "Test 6: flatten-list flattens nested expression lists")
!(test (flatten-list Nil) Nil)
!(test (flatten-list (Cons a (Cons b Nil))) (Cons a (Cons b Nil)))
!(test (flatten-list (Cons (a b) (Cons c Nil)))
       (Cons a (Cons b (Cons c Nil))))
!(test (flatten-list (Cons (x y) (Cons (p q) Nil)))
       (Cons x (Cons y (Cons p (Cons q Nil)))))

!(println! "Test 7: flatten-expr flattens nested expressions")
!(test (flatten-expr ((a b) c)) (a b c))
!(test (flatten-expr ((x) (y z))) (x y z))
!(test (flatten-expr ()) ())

!(println! "")
!(println! "=== All list operation tests complete ===")
