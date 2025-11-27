;; test_add_e_petta.metta - Test add_e function (PeTTa version)

!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)
!(import! &self ../mmverify-utils_petta)

;; Create test KB
!(bind! &kb (new-space))

;; Test 1: Add first essential hypothesis to level 1
!(add_e &kb label1 ("wff" "ph") 1)
!(test (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") Nil)))

;; Test 2: Add second essential hypothesis to same level (should append)
!(add_e &kb label2 ("wff" "ps") 1)
!(test (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") (Cons ("wff" "ps") Nil))))

;; Test 3: Verify EHyp atoms were created  
!(test (size-atom (collapse (match &kb ((Label $l) EHyp (FSDepth 1) $data) found))) 2)

;; Test 4: Add essential hypothesis to different level
!(add_e &kb label3 ("wff" "ch") 2)
!(test (collapse (match &kb (EList (FSDepth 2) $elist) $elist)) ((Cons ("wff" "ch") Nil)))

;; Test 5: Verify level 1 EList unchanged
!(test (collapse (match &kb (EList (FSDepth 1) $elist) $elist)) ((Cons ("wff" "ph") (Cons ("wff" "ps") Nil))))
