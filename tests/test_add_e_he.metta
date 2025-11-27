;; test_add_e_he.metta - Test add_e function (HE version)

!(import! &self mmverify-utils)

;; Create test KB
!(bind! &kb (new-space))

;; Test 1-5: add_e functionality
!(add_e &kb label1 ("wff" "ph") 1)
!(assertEqual (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") Nil)))

!(add_e &kb label2 ("wff" "ps") 1)
!(assertEqual (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") (Cons ("wff" "ps") Nil))))

!(assertEqual (size-atom (collapse (match &kb ((Label $l) EHyp (FSDepth 1) $data) found))) 2)

!(add_e &kb label3 ("wff" "ch") 2)
!(assertEqual (collapse (match &kb (EList (FSDepth 2) $elist) $elist)) ((Cons ("wff" "ch") Nil)))

!(assertEqual (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") (Cons ("wff" "ps") Nil))))
