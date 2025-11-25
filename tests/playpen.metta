!(include demo0_bc)
!(include metamath)

!(get-atoms &kb')
!(get-atoms &md)

!(match &md $d (println! $d))
!(match &md $d (add-atom &self $d))

!(include demo0_nil)

!(bc &kbh (fromNumber 5)
      (: (mp $1
             $2
             (a2 $3)
             (mp $4
                 $5
                 (a2 $6)
                 (a1 $7 $8 $9)))
         (⟨=⟩ ⟨t⟩ ⟨t⟩)))

; !(bind! &mb (new-space))
; !(match &md (MeTTaData $d) (add-atom &mb $d))

; ((Label ⟨mp⟩) Assertion ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ((⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))) (Statement (⟨|-⟩ ⟨Q⟩)) (Type "$a") 
;     (MeTTaImp 
;         (-> (⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) (⟨|-⟩ ⟨Q⟩))
;     )))

; ((Label ⟨a2⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩)) (Type "$a") 
; 	(MeTTaImp 
;         (-> (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))
;     )))

; [(Constant ⟨0⟩ (Type "$c")), (Constant ⟨+⟩ (Type "$c")), (Constant ⟨=⟩ (Type "$c")), (Constant ⟨->⟩ (Type "$c")), (Constant ⟨⟦⟩ (Type "$c")), (Constant ⟨⟧⟩ (Type "$c")), (Constant ⟨term⟩ (Type "$c")), (Constant ⟨wff⟩ (Type "$c")), (Constant ⟨|-⟩ (Type "$c")), ((Label ⟨tze⟩) Assertion ((DVars ()) (FHyps ()) (EHyps ()) (Statement (⟨term⟩ ⟨0⟩)) (Type "$a") (MeTTaImp (: ⟨tze⟩ (⟨term⟩ ⟨0⟩))))), ((Label ⟨tpl⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩))) (EHyps ()) (Statement (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨tpl⟩ (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩))))), ((Label ⟨weq⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩))) (EHyps ()) (Statement (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩)) (Type "$a") (MeTTaImp (: ⟨weq⟩ (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩))))), ((Label ⟨wim⟩) Assertion ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ()) (Statement (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨wim⟩ (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))))), ((Label ⟨a1⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩) (⟨term⟩ ⟨s⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨a1⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩))))), 

((Label ⟨a2⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩)) (Type "$a") 
    (MeTTaImp 
        (: ⟨a2⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))
    )
)) 

((Label ⟨mp⟩) Assertion ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ((⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))) (Statement (⟨|-⟩ ⟨Q⟩)) (Type "$a") 
    (MeTTaImp 
        (: ⟨mp⟩ (-> (⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) (⟨|-⟩ ⟨Q⟩)))
    )
))

!(match &kb ((Label ⟨mp⟩) Assertion ((DVars $dvs) (FHyps $f_hyps) (EHyps $e_hyps) (Statement $stmt) (Type $type) (MeTTaImp $mimp))) $f_hyps)

[(Constant ⟨0⟩ (Type "$c")), (Constant ⟨+⟩ (Type "$c")), (Constant ⟨=⟩ (Type "$c")), (Constant ⟨->⟩ (Type "$c")), (Constant ⟨⟦⟩ (Type "$c")), (Constant ⟨⟧⟩ (Type "$c")), (Constant ⟨term⟩ (Type "$c")), (Constant ⟨wff⟩ (Type "$c")), (Constant ⟨|-⟩ (Type "$c")), ((Label ⟨tze⟩) Assertion ((DVars ()) (FHyps ()) (EHyps ()) (Statement (⟨term⟩ ⟨0⟩)) (Type "$a") (MeTTaImp (: ⟨tze⟩ (⟨term⟩ ⟨0⟩))))), ((Label ⟨tpl⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩))) (EHyps ()) (Statement (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨tpl⟩ (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩))))), ((Label ⟨weq⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩))) (EHyps ()) (Statement (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩)) (Type "$a") (MeTTaImp (: ⟨weq⟩ (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩))))), ((Label ⟨wim⟩) Assertion ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ()) (Statement (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨wim⟩ (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))))), ((Label ⟨a1⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩) (⟨term⟩ ⟨r⟩) (⟨term⟩ ⟨s⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩)) (Type "$a") (MeTTaImp (: ⟨a1⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩))))), ((Label ⟨a2⟩) Assertion ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩)) (Type "$a") (MeTTaImp (: ⟨a2⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))))), ((Label ⟨mp⟩) Assertion ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ((⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))) (Statement (⟨|-⟩ ⟨Q⟩)) (Type "$a") (MeTTaImp (: ⟨mp⟩ (-> (⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) (⟨|-⟩ ⟨Q⟩)))))), ((Label ⟨th1⟩) Proof ((DVars ()) (FHyps ((⟨term⟩ ⟨t⟩))) (EHyps ()) (Statement (⟨|-⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩)) (Type "$p") 

(MeTTaImp (: ⟨th1⟩ (⟨|-⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩))) 

(ProofSequence (⟨tt⟩ ⟨tze⟩ ⟨tpl⟩ ⟨tt⟩ ⟨weq⟩ ⟨tt⟩ ⟨tt⟩ ⟨weq⟩ ⟨tt⟩ ⟨a2⟩ ⟨tt⟩ ⟨tze⟩ ⟨tpl⟩ ⟨tt⟩ ⟨weq⟩ ⟨tt⟩ ⟨tze⟩ ⟨tpl⟩ ⟨tt⟩ ⟨weq⟩ ⟨tt⟩ ⟨tt⟩ ⟨weq⟩ ⟨wim⟩ ⟨tt⟩ ⟨a2⟩ ⟨tt⟩ ⟨tze⟩ ⟨tpl⟩ ⟨tt⟩ ⟨tt⟩ ⟨a1⟩ ⟨mp⟩ ⟨mp⟩))))]

[
    (: ⟨tze⟩ (⟨term⟩ ⟨0⟩)), 
    (: ⟨tpl⟩ (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩)), 
    (: ⟨weq⟩ (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩)), 
    (: ⟨wim⟩ (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩)), 
    (: ⟨a1⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩)), 
    (: ⟨a2⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩)), 
    (: ⟨mp⟩ (-> (⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) (⟨|-⟩ ⟨Q⟩))), 
    (: ⟨th1⟩ (⟨|-⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩))]

> !(match &md (MeTTaData $d) (println! $d))
(: ⟨mp⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) (⟨|-⟩ ⟨Q⟩)))
(: ⟨a2⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))
(: ⟨a1⟩ (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩))
(: ⟨wim⟩ (⟨wff⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))
(: ⟨weq⟩ (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩))
(: ⟨tpl⟩ (⟨term⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩))
(: ⟨tze⟩ (⟨term⟩ ⟨0⟩))
(: ⟨Q⟩ ⟨wff⟩)
(: ⟨Q⟩ var)
(: ⟨P⟩ ⟨wff⟩)
(: ⟨P⟩ var)
(: ⟨s⟩ ⟨term⟩)
(: ⟨s⟩ var)
(: ⟨r⟩ ⟨term⟩)
(: ⟨r⟩ var)
(: ⟨t⟩ ⟨term⟩)
(: ⟨t⟩ var)
(: ⟨|-⟩ const)
(: ⟨wff⟩ const)
(: ⟨term⟩ const)
(: ⟨⟧⟩ const)
(: ⟨⟦⟩ const)
(: ⟨->⟩ const)
(: ⟨=⟩ const)
(: ⟨+⟩ const)
(: ⟨0⟩ const)

> !(bc &mb Nil (fromNumber 2) (: $proof (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩)))

[(: ⟨weq⟩ (⟨wff⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩))]


(: ⟨th1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨mp⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: (⟨P⟩) ⟨|-⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨|-⟩) (: (⟨Q⟩) ⟨|-⟩)))
(: ⟨a2⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨a1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: ⟨s⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩) ⟨|-⟩)))
(: ⟨wim⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨wff⟩)))
(: ⟨weq⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)))
(: ⟨tpl⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩)))
(: ⟨tze⟩ (: ⟨term⟩ (⟨0⟩)))
(: ⟨Q⟩ ⟨wff⟩)
(: ⟨Q⟩ var)
(: ⟨P⟩ ⟨wff⟩)
(: ⟨P⟩ var)
(: ⟨s⟩ ⟨term⟩)
(: ⟨s⟩ var)
(: ⟨r⟩ ⟨term⟩)
(: ⟨r⟩ var)
(: ⟨t⟩ ⟨term⟩)
(: ⟨t⟩ var)
(: ⟨|-⟩ const)
(: ⟨wff⟩ const)
(: ⟨term⟩ const)
(: ⟨⟧⟩ const)
(: ⟨⟦⟩ const)
(: ⟨->⟩ const)
(: ⟨=⟩ const)
(: ⟨+⟩ const)
(: ⟨0⟩ const)

!(bind! &mb (new-space))
!(match &md (MeTTaData $d) (add-atom &mb $d))

(: ⟨th1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨mp⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: ⟨P⟩ ⟨|-⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨|-⟩) (: ⟨Q⟩ ⟨|-⟩)))
(: ⟨a2⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨a1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: ⟨s⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩) ⟨|-⟩)))
(: ⟨wim⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨wff⟩)))
(: ⟨weq⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)))
(: ⟨tpl⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩)))
(: ⟨tze⟩ (: ⟨0⟩ ⟨term⟩))
(: ⟨Q⟩ ⟨wff⟩)
(: ⟨Q⟩ var)
(: ⟨P⟩ ⟨wff⟩)
(: ⟨P⟩ var)
(: ⟨s⟩ ⟨term⟩)
(: ⟨s⟩ var)
(: ⟨r⟩ ⟨term⟩)
(: ⟨r⟩ var)
(: ⟨t⟩ ⟨term⟩)
(: ⟨t⟩ var)
(: ⟨|-⟩ const)
(: ⟨wff⟩ const)
(: ⟨term⟩ const)
(: ⟨⟧⟩ const)
(: ⟨⟦⟩ const)
(: ⟨->⟩ const)
(: ⟨=⟩ const)
(: ⟨+⟩ const)
(: ⟨0⟩ const)

(: tpl-proper (-> (: $t#1342781 ⟨term⟩) (: $r#1342782 ⟨term⟩) (: (⟨⟦⟩ $t#1342781 ⟨+⟩ $r#1342782 ⟨⟧⟩) ⟨term⟩)))
(: mp (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: $⟨P⟩ ⟨|-⟩) (: (⟨⟦⟩ $⟨P⟩ ⟨->⟩ $⟨Q⟩ ⟨⟧⟩) ⟨|-⟩) (: $⟨Q⟩ ⟨|-⟩)))

!(bc &mb Nil (fromNumber 3) (: $proof (: ⟨Q⟩ ⟨|-⟩)))

!(add-atom &mb (: ⟨weq⟩ (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨r⟩) ⟨wff⟩))))

!(bc &mb Nil (fromNumber 3) (: $proof (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)))

> !(add-atom &mb (: ⟨tr⟩ (: ⟨r⟩ ⟨term⟩)))
[()]
> !(add-atom &mb (: ⟨weq⟩ (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨r⟩) ⟨wff⟩))))

!(bc &mb Nil (fromNumber 3) (: $proof (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)))
[()]
[(: (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)), (: (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩))]


> !(bc &mb' 
     (Cons (: p1 (⟨|-⟩ ⟨P⟩))
           (Cons (: p2 (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))
                 Nil))
     (fromNumber 2)
     (: $proof (⟨|-⟩ ⟨Q⟩)))
[(: (⟨mp⟩ p1 p2) (⟨|-⟩ ⟨Q⟩))]

[(: (tpl-proper (tpl-proper (tpl-proper ⟨tze⟩ ⟨tze⟩) ⟨tze⟩) ⟨tze⟩) (: (⟨⟦⟩ (⟨⟦⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper (tpl-proper (tpl-proper ⟨tze⟩ ⟨tze⟩) (tpl-proper ⟨tze⟩ ⟨tze⟩)) ⟨tze⟩) (: (⟨⟦⟩ (⟨⟦⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨⟧⟩) ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper (tpl-proper ⟨tze⟩ ⟨tze⟩) ⟨tze⟩) (: (⟨⟦⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper (tpl-proper ⟨tze⟩ (tpl-proper ⟨tze⟩ ⟨tze⟩)) ⟨tze⟩) (: (⟨⟦⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨⟧⟩) ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tze⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨0⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩))]

!(add-atom &mb (: tpl-proper (-> (: $t ⟨term⟩) (: $r ⟨term⟩) (: (⟨⟦⟩ $t ⟨+⟩ $r ⟨⟧⟩) ⟨term⟩))))

!(bc &mb (Cons (: tpl-proper (-> (: $t ⟨term⟩) (: $r ⟨term⟩) (: (⟨⟦⟩ $t ⟨+⟩ $r ⟨⟧⟩) ⟨term⟩))) (Cons (: ⟨tt⟩ (: ⟨t⟩ ⟨term⟩)) (Cons (: ⟨tze⟩ (: ⟨0⟩ ⟨term⟩)) Nil)))
     (fromNumber 3) (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)))

(: ⟨t⟩ ⟨term⟩)
(: ⟨0⟩ const)
(: ⟨tt⟩ (: ⟨t⟩ ⟨term⟩))

> !(bc &mb (Cons (: tpl-proper (-> (: $t ⟨term⟩) (: $r ⟨term⟩) (: (⟨⟦⟩ $t ⟨+⟩ $r ⟨⟧⟩) ⟨term⟩))) (Cons (: ⟨tt⟩ (: ⟨t⟩ ⟨term⟩)) (Cons (: ⟨tze⟩ (: ⟨0⟩ ⟨term⟩)) Nil)))
     (fromNumber 3) (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)))
[(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)), 
(: (tpl-proper ⟨tt⟩ ⟨tze⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩))]

> !(bc &mb Nil (fromNumber 3) (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)))

["(format-args {} (⟨t⟩))"]
> !(let $x (format-args ${} (⟨t⟩)) (repr $x))
["\"$⟨t⟩\""]
> !(let $x (format-args ${} (⟨t⟩)) (parse (repr $x)))
["$⟨t⟩"]
> !(let $x (format-args ${} (⟨t⟩)) (parse (parse (repr $x))))
[$⟨t⟩]

(let $vtok (fromat-args ${} ($tok)) (parse (parse (repr $vtok)))) 
(= (make_var123 $x) (let $v (format-args ${} ($x)) (parse (parse (repr $v)))))
(= (make_var $x) (let $v (format-args ${} ($x)) (repr $v)))

(case $mtok 
    ( 
        ((v $tok) (let $vtok (repr $tok) $vtok)) 
        ($tok $tok)  ))


        (= (typify_assertion123 $assert)
  (match $assert (: $label (-> $args $typed_stmt))  ; Extract
    (let $prefixed_args  ; Prefix args
         (map-atom $args $arg  ; Each (: var type)
           (let ($var $type) (decons-atom $arg)  ; Split
             (cons-atom : (prefix_vars $var) $type)))  ; Rebuild prefixed
      (let $prefixed_stmt (prefix_vars $typed_stmt)  ; Prefix stmt
        (: $label (-> $prefixed_args $prefixed_stmt))))))  ; Reassemble

(= (map-list1234 Nil $fn) Nil)  ; Base: empty → empty
(= (map-list1234 (Cons $head $tail) $fn)
   (Cons ($fn $head) (map-list1234 $tail $fn)))  ; Apply fn to head, recurse tail

(= (map-list-pattern12 Nil $pattern) Nil)
(= (map-list-pattern12 (Cons $head $tail) $pattern)
   (let $tail-result (map-list-pattern12 $tail $pattern)
     (case (match &self $head $pattern)
       (($result (Cons $result $tail-result))
        (() $tail-result)))))

!(map-list-pattern12 &test-list (fact $x $value))

(= (map-list123' Nil $var $pattern) Nil)
(= (map-list123' (Cons $head $tail) $var $pattern)
   (let $tail-result (map-list123' $tail $var $pattern)
     (let $result (let $var $head $pattern)
       (Cons $result $tail-result))))

; Example 1: Wrap each element in a type declaration
!(map-list12' (Cons ⟨a⟩ (Cons ⟨b⟩ (Cons ⟨c⟩ Nil))) $x (: $x ⟨symbol⟩))
; Should return: (Cons (: ⟨a⟩ ⟨symbol⟩) (Cons (: ⟨b⟩ ⟨symbol⟩) (Cons (: ⟨c⟩ ⟨symbol⟩) Nil)))

; Example 2: Apply a transformation to numbers
!(map-list12' &test-numbers $n (+ $n 10))

(= (map-list Nil $var $pattern) Nil)
(= (map-list (Cons $head $tail) $var $pattern)
  (let $new-head (sealed ($var) (let $var $head $pattern))
    (Cons $new-head
          (map-list $tail $var $pattern))))

!(map-list (Cons ⟨a⟩ (Cons ⟨b⟩ (Cons ⟨c⟩ Nil))) $x ($x ⟨symbol⟩))
!(map-list (Cons ⟨a⟩ (Cons ⟨b⟩ (Cons ⟨c⟩ Nil))) $x (let $y ($x ⟨symbol⟩) (trace! ("y:" $y) $y)))


(= (map' Nil $var $pattern) Nil)
(= (map' (Cons $head $tail) $var $pattern)
  (trace! ($head - $tail - $var)
    (let $var $head
      (trace! ("var:" $var)
        (Cons $pattern
          (map' $tail $var $pattern))))))

(= (map' Nil $var $pattern) Nil)
(= (map' (Cons $head $tail) $var $pattern)
  (Cons (eval 
          (sealed ($var)  
            (unify $var $head
              $pattern ())))
        (map' $tail $var $pattern)))

(= (map-list Nil $function) Nil)
(= (map-list (Cons $head $tail) $function)
   (let $tail-result (map-list $tail $function)
     (let $result ($function $head)
       (Cons $result $tail-result))))

(= (map-list Nil $function) Nil)
(= (map-list (Cons $head $tail) $function)
   (let $tail-result (map-list $tail $function)
     (let $result ($function $head)
       (Cons $result $tail-result))))

(= (make_vardummy $x) (let $v (format-args "${}" ($x)) $v))

(= (make_var $x) (let $v (format-args "${}" ($x)) (parse (parse (repr $v)))))

(= (add_vars_to_stmt1 $space $stmt)
  (map-atom $stmt $tok (unify $space (: $tok var) (make_var $tok) $tok)))

!(match &mb (: ⟨tpl⟩ $imp) (let $flat_imp (flatten-expr $imp) ((map-atom $flat_imp $tok (unify &mb (: $tok var) (make_var $tok) $tok)))))

((: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩))

(: ⟨th1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨mp⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: ⟨P⟩ ⟨|-⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨|-⟩) (: ⟨Q⟩ ⟨|-⟩)))
(: ⟨a2⟩ (-> (: ⟨t⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
(: ⟨a1⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: ⟨s⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨r⟩ ⟨->⟩ ⟨⟦⟩ ⟨t⟩ ⟨=⟩ ⟨s⟩ ⟨->⟩ ⟨r⟩ ⟨=⟩ ⟨s⟩ ⟨⟧⟩ ⟨⟧⟩) ⟨|-⟩)))
(: ⟨wim⟩ (-> (: ⟨P⟩ ⟨wff⟩) (: ⟨Q⟩ ⟨wff⟩) (: (⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩) ⟨wff⟩)))
(: ⟨weq⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨wff⟩)))
(: ⟨tpl⟩ (-> (: ⟨t⟩ ⟨term⟩) (: ⟨r⟩ ⟨term⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩)))
(: ⟨tze⟩ (: ⟨0⟩ ⟨term⟩))
(: ⟨Q⟩ ⟨wff⟩)
(: ⟨Q⟩ var)
(: ⟨P⟩ ⟨wff⟩)
(: ⟨P⟩ var)
(: ⟨s⟩ ⟨term⟩)
(: ⟨s⟩ var)
(: ⟨r⟩ ⟨term⟩)
(: ⟨r⟩ var)
(: ⟨t⟩ ⟨term⟩)
(: ⟨t⟩ var)
(: ⟨|-⟩ const)
(: ⟨wff⟩ const)
(: ⟨term⟩ const)
(: ⟨⟧⟩ const)
(: ⟨⟦⟩ const)
(: ⟨->⟩ const)
(: ⟨=⟩ const)
(: ⟨+⟩ const)
(: ⟨0⟩ const)

(: ⟨th1⟩ (-> (: $⟨t⟩#39345 ⟨term⟩) (: ($⟨t⟩#39345 ⟨=⟩ $⟨t⟩#39345) ⟨|-⟩)))
(: ⟨mp⟩ (-> (: $⟨P⟩#39348 ⟨wff⟩) (: $⟨Q⟩#39349 ⟨wff⟩) (: $⟨P⟩#39348 ⟨|-⟩) (: (⟨⟦⟩ $⟨P⟩#39348 ⟨->⟩ $⟨Q⟩#39349 ⟨⟧⟩) ⟨|-⟩) (: $⟨Q⟩#39349 ⟨|-⟩)))
(: ⟨a2⟩ (-> (: $⟨t⟩#39345 ⟨term⟩) (: (⟨⟦⟩ $⟨t⟩#39345 ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ $⟨t⟩#39345) ⟨|-⟩)))
(: ⟨a1⟩ (-> (: $⟨t⟩#39345 ⟨term⟩) (: $⟨r⟩#39346 ⟨term⟩) (: $⟨s⟩#39347 ⟨term⟩) (: (⟨⟦⟩ $⟨t⟩#39345 ⟨=⟩ $⟨r⟩#39346 ⟨->⟩ ⟨⟦⟩ $⟨t⟩#39345 ⟨=⟩ $⟨s⟩#39347 ⟨->⟩ $⟨r⟩#39346 ⟨=⟩ $⟨s⟩#39347 ⟨⟧⟩ ⟨⟧⟩) ⟨|-⟩)))
(: ⟨wim⟩ (-> (: $⟨P⟩#39348 ⟨wff⟩) (: $⟨Q⟩#39349 ⟨wff⟩) (: (⟨⟦⟩ $⟨P⟩#39348 ⟨->⟩ $⟨Q⟩#39349 ⟨⟧⟩) ⟨wff⟩)))
(: ⟨weq⟩ (-> (: $⟨t⟩#39345 ⟨term⟩) (: $⟨r⟩#39346 ⟨term⟩) (: ($⟨t⟩#39345 ⟨=⟩ $⟨r⟩#39346) ⟨wff⟩)))
(: ⟨tpl⟩ (-> (: $⟨t⟩#39345 ⟨term⟩) (: $⟨r⟩#39346 ⟨term⟩) (: (⟨⟦⟩ $⟨t⟩#39345 ⟨+⟩ $⟨r⟩#39346 ⟨⟧⟩) ⟨term⟩)))
(: ⟨tze⟩ (-> (: ⟨0⟩ ⟨term⟩)))
(: ⟨wq⟩ (: $⟨Q⟩#39349 ⟨wff⟩))
(: ⟨wp⟩ (: $⟨P⟩#39348 ⟨wff⟩))
(: ⟨ts⟩ (: $⟨s⟩#39347 ⟨term⟩))
(: ⟨tr⟩ (: $⟨r⟩#39346 ⟨term⟩))
(: ⟨tt⟩ (: $⟨t⟩#39345 ⟨term⟩))
(: ⟨Q⟩ Var)
(: ⟨P⟩ Var)
(: ⟨s⟩ Var)
(: ⟨r⟩ Var)
(: ⟨t⟩ Var)
(: ⟨|-⟩ Const)
(: ⟨wff⟩ Const)
(: ⟨term⟩ Const)
(: ⟨⟧⟩ Const)
(: ⟨⟦⟩ Const)
(: ⟨->⟩ Const)
(: ⟨=⟩ Const)
(: ⟨+⟩ Const)


!(bc &md (Cons (: ⟨tpl⟩ (-> (: $t ⟨term⟩) (: $r ⟨term⟩) (: (⟨⟦⟩ $t ⟨+⟩ $r ⟨⟧⟩) ⟨term⟩))) (Cons (: ⟨tt⟩ (: ⟨t⟩ ⟨term⟩)) (Cons (: ⟨tze⟩ (: ⟨0⟩ ⟨term⟩)) Nil)))
     (fromNumber 3) (: $proof (: ((⟨⟦⟩) ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)))

!(bc &md Nil (fromNumber 3) (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨term⟩)))

!(bc &md Nil (fromNumber 3) (: $proof (: ( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨term⟩)))


!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: (⟨⟦⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩)))
[(: (⟨tpl⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tr⟩) (: (⟨⟦⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨+⟩ ⟨r⟩ ⟨⟧⟩) ⟨term⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

;; Don't work
; !(bc &md
;      Nil
;      (fromNumber 3)
;      (: $proof (: (⟨⟦⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩ ⟨⟧⟩) ⟨wff⟩)))

; !(bc &md
;      Nil
;      (fromNumber 4)
;      (: $proof (: (⟨⟦⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨⟦⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨⟧⟩) ⟨⟧⟩) ⟨|-⟩)))

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: (⟨⟦⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨⟧⟩) ⟨wff⟩)))
     [(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (⟨weq⟩ ⟨tt⟩ ⟨tt⟩)) (: (⟨⟦⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨⟧⟩) ⟨wff⟩))]
;; "t" "=" "t"

 !(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (: (⟨weq⟩ tplus0 ⟨tt⟩) (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨th1⟩ ⟨tt⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

;; Good case study for the parens issue.

> !(bc &md Nil (fromNumber 3) (: $proof (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

;; Cuz the following is how MM would do it, right?  It is precisely the wff in a2
(: ⟨a2⟩ (-> (: $⟨t⟩ ⟨term⟩) (: (⟨⟦⟩ $⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ $⟨t⟩) ⟨|-⟩)))
> !(bc &md Nil (fromNumber 3) (: $proof (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
!(add-atom &md (: ⟨a2⟩ (-> (: $⟨t⟩ ⟨term⟩) (: (( $⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ $⟨t⟩) ⟨|-⟩))))

> !(bc &md Nil (fromNumber 3) (: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))

---

Ok, I now use parentheses:

> !(bc &md Nil (fromNumber 3) (: $proof (: ( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨term⟩)))
[]
> !(bc &md Nil (fromNumber 3) (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ )) ⟨term⟩)))
[(: (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩)) ⟨term⟩))]

;; Comment: perhaps the ()s are now getting duplicated?

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: (( (( ⟨t⟩ ⟨+⟩ ⟨0⟩ )) ⟨+⟩ ⟨r⟩ )) ⟨term⟩)))
[(: (⟨tpl⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tr⟩) (: ((((⟨t⟩ ⟨+⟩ ⟨0⟩)) ⟨+⟩ ⟨r⟩)) ⟨term⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: (( (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) )) ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (⟨weq⟩ ⟨tt⟩ ⟨tt⟩)) (: (((⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩))) ⟨wff⟩))]

 !(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: ((( ⟨t⟩ ⟨+⟩ ⟨0⟩ )) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: (((⟨t⟩ ⟨+⟩ ⟨0⟩)) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: ((( ⟨t⟩ ⟨+⟩ ⟨0⟩ )) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: (((⟨t⟩ ⟨+⟩ ⟨0⟩)) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

;; old a2
(: ⟨a2⟩ (-> (: $⟨t⟩ ⟨term⟩) (: (⟨⟦⟩ $⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ $⟨t⟩) ⟨|-⟩)))
;; new a2
(: ⟨a2⟩ (-> (: $⟨t⟩ ⟨term⟩) (: (( $⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ $⟨t⟩) ⟨|-⟩))))

> !(bc &md Nil (fromNumber 5) (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))

;; Fix doubled up parentheses:

!(bc &md
     Nil
     (fromNumber 3)
     (: $proof (: ( (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (⟨weq⟩ ⟨tt⟩ ⟨tt⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &md Nil (fromNumber 5) (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md Nil (fromNumber 3) (: $proof (: ( ⟨r⟩ ⟨=⟩ ⟨s⟩ ) ⟨wff⟩)))
[(: (⟨weq⟩ ⟨tr⟩ ⟨ts⟩) (: (⟨r⟩ ⟨=⟩ ⟨s⟩) ⟨wff⟩))]

> !(let $p (bc &md Nil (fromNumber 3) (: $proof (: ( ⟨t⟩ ⟨=⟩ ⟨s⟩ ) ⟨wff⟩))) (add-atom &md $p))
[()]
> !(let $p (bc &md Nil (fromNumber 3) (: $proof (: ( ⟨r⟩ ⟨=⟩ ⟨s⟩ ) ⟨wff⟩))) (add-atom &md $p))
[()]


> !(bc &md Nil (fromNumber 5) (: $proof (: ( ( ⟨t⟩ ⟨=⟩ ⟨s⟩ ) ⟨->⟩ ( ⟨r⟩ ⟨=⟩ ⟨s⟩ ) )  ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩)) ⟨wff⟩))]

> !(bc &md Nil (fromNumber 5) (: $proof (: ( ( ⟨t⟩ ⟨=⟩ ⟨s⟩ ) ⟨->⟩ ( ⟨r⟩ ⟨=⟩ ⟨s⟩ ) )  ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩)) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩)) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩)) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩)) ⟨wff⟩))]

!(bc &md Nil (fromNumber 7) (: $proof 
  (: 
    ( 
      ( ⟨t⟩ ⟨=⟩ ⟨r⟩ ) 
        ⟨->⟩ 
      ( ( ⟨t⟩ ⟨=⟩ ⟨s⟩ ) 
          ⟨->⟩ 
        ( ⟨r⟩ ⟨=⟩ ⟨s⟩ ) 
      ) 
    ) ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩))) (: ((⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨->⟩ ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩))) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩))) (: ((⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨->⟩ ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩))) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩))) (: ((⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨->⟩ ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩))) ⟨wff⟩)), (: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tr⟩) (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨ts⟩) (⟨weq⟩ ⟨tr⟩ ⟨ts⟩))) (: ((⟨t⟩ ⟨=⟩ ⟨r⟩) ⟨->⟩ ((⟨t⟩ ⟨=⟩ ⟨s⟩) ⟨->⟩ (⟨r⟩ ⟨=⟩ ⟨s⟩))) ⟨wff⟩))]

!(bc &md
     Nil
     (fromNumber 2)
     (: $proof (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &md Nil (fromNumber 3) (: $proof 
  (: 
    ( ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
        ⟨->⟩ 
      ( ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
          ⟨->⟩ 
        (⟨t⟩ ⟨=⟩ ⟨t⟩) 
      ) 
    ) 
  
    ⟨|-⟩)))

!(add-atom &md (: ⟨a1'⟩ (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: $⟨s⟩ ⟨term⟩) (: ( ($⟨t⟩ ⟨=⟩ $⟨r⟩) ⟨->⟩ ( ($⟨t⟩ ⟨=⟩ $⟨s⟩) ⟨->⟩ ($⟨r⟩ ⟨=⟩ $⟨s⟩) ) ) ⟨|-⟩))))

!(bc &md Nil (fromNumber 3) (: $proof 
  (: 
    ( 
        ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
          ⟨->⟩ 
        ( ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
          ⟨->⟩ 
        (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ) 
    ⟨|-⟩)))

> !(bc &md Nil (fromNumber 3) (: $proof 
  (: 
    ( 
        ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
          ⟨->⟩ 
        ( 
            ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) 
              ⟨->⟩ 
            (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ) ⟨|-⟩)))

!(bc &md
     Nil
     (fromNumber 2)
     (: (⟨a2⟩ $t) (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

> !(bc &md Nil (fromNumber 3)
   (: $proof (: (⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨term⟩)))
[(: (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) (: (⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨term⟩))]
> !(bc &md Nil (fromNumber 3)
   (: $proof (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨+⟩ ⟨r⟩) ⟨term⟩)))
[(: (⟨tpl⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tr⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨+⟩ ⟨r⟩) ⟨term⟩))]
> 

!(bc &md Nil (fromNumber 2)
   (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

!(bc &md Nil (fromNumber 5) 
   (: (⟨a1⟩ $t $r $s)
      (: 
        ( ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ 
           ( ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ) 
      ⟨|-⟩)))

!(bc &md
   (Cons (: ⟨tt⟩   (: ⟨t⟩ ⟨term⟩))
         (Cons (: tplus0 (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨term⟩)) Nil)))
   (fromNumber 3)
   (: $proof (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)), (match' (Cons (: tplus0 (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨term⟩)) Nil)) (: $proof (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)) (: $proof (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))]

;; Weird, AIs, why do you think the match' is there?  Look at the bc etc.

!(bc &md
   Nil
   (fromNumber 3)
   (: $proof (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
[(: (⟨weq⟩ (⟨tpl⟩ ⟨tt⟩ ⟨tze⟩) ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩))]

;; AIs, so far it's more effective w/o the short-cuts.  If it can generate it, it can generate it.

!(bc &md Nil (fromNumber 3)
   (: $proof
      (: ((⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨wff⟩)))
[(: (⟨wim⟩ (⟨weq⟩ ⟨tt⟩ ⟨tt⟩) (⟨weq⟩ ⟨tt⟩ ⟨tt⟩)) (: ((⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨wff⟩))]

!(bc &md Nil (fromNumber 2)
   (: (⟨a2⟩ ⟨tt⟩)
      (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: (⟨a2⟩ ⟨tt⟩) (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

(»»» treating label ⟨mp⟩)
(Assertion ⟨mp⟩ data: ((DVars ()) (FHyps ((⟨wff⟩ ⟨P⟩) (⟨wff⟩ ⟨Q⟩))) (EHyps ((⟨|-⟩ ⟨P⟩) (⟨|-⟩ ⟨⟦⟩ ⟨P⟩ ⟨->⟩ ⟨Q⟩ ⟨⟧⟩))) (Statement (⟨|-⟩ ⟨Q⟩)) (Type "$a")))
(stack_len: 4.0 , npop: 4 , sp: 0.0)
("adding subst" ⟨P⟩ (⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))
("adding subst" ⟨Q⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩))
(new_conclusion: (⟨|-⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩))

!(add-atom &md (: ⟨a1⟩ (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: $⟨s⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨=⟩ $⟨r⟩ ⟨->⟩ ( $⟨t⟩ ⟨=⟩ $⟨s⟩ ⟨->⟩ $⟨r⟩ ⟨=⟩ $⟨s⟩ ) ) ⟨|-⟩))))
!(add-atom &md (: ⟨mp⟩ (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: $⟨P⟩ ⟨|-⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨|-⟩) (: $⟨Q⟩ ⟨|-⟩))))


!(bc &md 
   (Cons (: premise1 (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩))
         (Cons (: premise2 (: (( (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) )) ⟨|-⟩))
               Nil))
   (fromNumber 2)
   (: (⟨mp⟩ premise1 premise2) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))

;; Ah, we run into this match' again!
> !(bc &md
     (Cons (: p1 (⟨|-⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩))  ; |- P (with P = (t + 0) = t)
           (Cons (: p2 (⟨|-⟩ ⟨⟦⟩ ⟨⟦⟩ ⟨t⟩ ⟨+⟩ ⟨0⟩ ⟨⟧⟩ ⟨=⟩ ⟨t⟩ ⟨->⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩ ⟨⟧⟩))  ; |- (P -> Q)
                 Nil))
     (fromNumber 5)
     (: $proof (⟨|-⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩)))
[]
> !(match &md (: $label $_) $label)
[⟨0⟩, ⟨+⟩, ⟨=⟩, ⟨->⟩, ⟨⟦⟩, ⟨⟧⟩, ⟨term⟩, ⟨wff⟩, ⟨|-⟩, ⟨t⟩, ⟨r⟩, ⟨s⟩, ⟨P⟩, ⟨Q⟩, ⟨tt⟩, ⟨tr⟩, ⟨ts⟩, ⟨wp⟩, ⟨wq⟩, ⟨tze⟩, ⟨tpl⟩, ⟨weq⟩, ⟨wim⟩, ⟨a1⟩, ⟨a2⟩, ⟨mp⟩]

> !(add-atom &md (: ⟨mp-simple⟩ (-> (: $P ⟨|-⟩) (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
[()]
> !(bc &md 
   (Cons (: premise1 (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩))
         (Cons (: premise2 (: (( (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ⟨|-⟩))
               Nil)))
   (fromNumber 2)
   (: (⟨mp-simple⟩ premise1 premise2) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(match' (Cons (: premise2 (: ((((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)) Nil)) (: (⟨mp-simple⟩ premise1 premise2) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)) (: (⟨mp-simple⟩ premise1 premise2) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))]

> !(add-atom &md (: ⟨mp-simple⟩ 
  (-> (: $P ⟨|-⟩) (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
!(add-atom &md (: ⟨mp⟩ 
  (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: $⟨P⟩ ⟨|-⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨|-⟩) (: $⟨Q⟩ ⟨|-⟩))))

!(add-atom &md (: ⟨mp-curry⟩ 
  (-> (: $P ⟨wff⟩)                    ; P is a wff
    (-> (: $Q ⟨wff⟩)                  ; Q is a wff  
      (-> (: $P ⟨|-⟩)                 ; P is provable
        (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩)     ; (P -> Q) is provable
          (: $Q ⟨|-⟩)))))))           ; conclusion: Q is provable

;; ── prem1  :  ⊢ (t + 0) = t     ← from axiom a2
!(add-atom &md
   (: prem1 (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))

;; ── prem2  :  ⊢ ((t + 0) = t → t = t)   ← a1 instantiated
!(add-atom &md
   (: prem2
      (: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)))

!(bc &md 
   (Cons (: wff1 (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨wff⟩))
         (Cons (: wff2 (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩))
               (Cons (: premise1 (: (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨|-⟩))
                     (Cons (: premise2 (: (( (( ⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩) ) ⟨|-⟩)))
                           Nil))))
   (fromNumber 4)
   (: (⟨mp-curry⟩ wff1 wff2 premise1 premise2) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
;; Doesn't work.

!(bc &md
   ;; ── env slot with the two essential hypotheses ─────────
   Nil
   ;; ── search depth: needs to build the two wff‑premisses
   (fromNumber 4)
   ;; ── goal ───────────────────────────────────────────────
   (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
;; Also doesn't work.

!(add-atom &self
   (: wffP (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
!(add-atom &self
   (: wffQ (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨wff⟩)))
!(add-atom &self
   (: seqP (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
!(add-atom &self
   (: seqPQ
      (: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩)
            ⟨->⟩
           (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)))

> !(mp wffP wffQ seqP seqPQ)
[(mp wffP wffQ seqP seqPQ)]
> !(get-type (mp wffP wffQ seqP seqPQ))
[(: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)]
;; Cool!  It works.

!(bc &self
   Nil
   (fromNumber 4)                   
   (: (mp wffP wffQ seqP seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
;; Doesn't work

> !(get-type (mp-curry wffP))
[(-> (: $Q#283275 ⟨wff⟩) (-> (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩) (-> (: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ $Q#283275) ⟨|-⟩) (: $Q#283275 ⟨|-⟩))))]
> !(get-type ((mp-curry wffP) wffQ))
[(-> (: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨|-⟩) (-> (: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))]
> !(get-type (((mp-curry wffP) wffQ) seqP))
[(-> (: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]
> !(get-type ((((mp-curry wffP) wffQ) seqP) seqPQ))
[(: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)]
;; SO COOL!

!(add-atom &self (: mp-curry
  (-> (: $P ⟨wff⟩)                    ; P is a wff
    (-> (: $Q ⟨wff⟩)                  ; Q is a wff  
      (-> (: $P ⟨|-⟩)                 ; P is provable
        (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩)     ; (P -> Q) is provable
          (: $Q ⟨|-⟩)))))))           ; conclusion: Q is provable

!(add-atom &md (: a1 
  (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: $⟨s⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨=⟩ $⟨r⟩ ⟨->⟩ ( $⟨t⟩ ⟨=⟩ $⟨s⟩ ⟨->⟩ $⟨r⟩ ⟨=⟩ $⟨s⟩ ) ) ⟨|-⟩))))

!(add-atom &self (: a1-curry 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: ($t ⟨=⟩ $r ⟨->⟩ ($t ⟨=⟩ $s ⟨->⟩ $r ⟨=⟩ $s)) ⟨|-⟩))))))

!(add-atom &self (: a1-curry' 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: (($t ⟨=⟩ $r) ⟨->⟩ (($t ⟨=⟩ $s) ⟨->⟩ ($r ⟨=⟩ $s))) ⟨|-⟩))))))

!(bc &self
   Nil
   (fromNumber 4)                   
   (: ((((mp-curry wffP) wffQ) seqP) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: ((((mp-curry wffP) wffQ) seqP) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

⟨a2⟩ ⟨tt⟩

!(bc &self
   Nil
   (fromNumber 4)                   
   (: ((((mp-curry wffP) wffQ) (a2 tt)) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: ((((mp-curry wffP) wffQ) (a2 tt)) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &self
   Nil
   (fromNumber 10)                   
   (: ((((mp-curry (weq (tpl tt tze) tt))  (weq tt tt)) (a2 tt)) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
[(: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) seqPQ) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

!(bc &self
   Nil
   (fromNumber 7)                   
   (: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩) ))

!(bc &self
   Nil
   (fromNumber 7)                   
   (: 
    ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) 
      ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) 
        (((a1-curry' $tpltttze) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩) ))

$weqtt

α-degenerates

(kb (: ⟨a2⟩ (-> (: $a ⟨term⟩) (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩))))
(kb (: ⟨a1⟩ (-> (: $a ⟨term⟩) (: $b ⟨term⟩) (: $c ⟨term⟩) (: (⟨->⟩ (⟨=⟩ $a $b) (⟨->⟩ (⟨=⟩ $a $c) (⟨=⟩ $b $c))) ⟨|-⟩))))
(kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩))))


(exec assemble-final-proof-direct
  (, (ev (: $P ⟨wff⟩))
     (ev (: $Q ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
;     (ev (: (⟨->⟩ $P ;; why is this needed?
;               (⟨->⟩ $P $Q))) ⟨|-⟩)
     (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
     (kb (: ⟨mp-curry⟩ (-> (: $P ⟨wff⟩) (-> (: $Q ⟨wff⟩)
                  (-> (: $P ⟨|-⟩) (-> (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩))))))) )
  (, (ev (: $Q ⟨|-⟩)
         ((((⟨mp-curry⟩ (: $P ⟨wff⟩))
            (: $Q ⟨wff⟩))
           (: $P ⟨|-⟩))
          (: (⟨->⟩ $P
                  (⟨->⟩ $P
                         $Q)) ⟨|-⟩)))))

; Intermediate step: derive (P -> Q) from P and (P -> (P -> Q))
(exec derive-P-to-Q-direct
  (, (ev (: (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) ⟨wff⟩))
     (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) (⟨=⟩ ⟨t⟩ ⟨t⟩)) ⟨wff⟩))
     (ev (: (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) ⟨|-⟩))
     (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩)
               (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩)
                       (⟨=⟩ ⟨t⟩ ⟨t⟩))) ⟨|-⟩))
     (kb (: ⟨mp-curry⟩ $_)))
  (, (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩) (⟨=⟩ ⟨t⟩ ⟨t⟩)) ⟨|-⟩)) ))  

(exec derive-P-to-Q-direct
  (, (ev (: $P ⟨wff⟩))
     (ev (: (⟨->⟩ $P $Q) ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
     (ev (: (⟨->⟩ $P
               (⟨->⟩ $P $Q)) ⟨|-⟩))
     (kb (: ⟨mp-curry⟩ (-> (: $P ⟨wff⟩) (-> (: $Q ⟨wff⟩)
                  (-> (: $P ⟨|-⟩) (-> (: (⟨->⟩ $P  (⟨->⟩ $P $Q)) ⟨|-⟩) (: $Q ⟨|-⟩))))))) )
  (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩)) )) 

(exec assemble-final-proof-direct
  (, (ev (: $P ⟨wff⟩))
     (ev (: $Q ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
;     (ev (: (⟨->⟩ $P ;; why is this needed?  -- apparently it's not!
;               (⟨->⟩ $P $Q))) ⟨|-⟩)
     (ev (: (⟨->⟩ $P $Q) ⟨|-⟩)))
;     (kb (: ⟨mp-curry⟩ (-> (: $P ⟨wff⟩) (-> (: $Q ⟨wff⟩)
;                  (-> (: $P ⟨|-⟩) (-> (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩))))))) )
  (, (ev (: $Q ⟨|-⟩))))

  (exec tpl-apply
  (, (ev (: $x ⟨term⟩))
     (ev (: $y ⟨term⟩)))
  (, (ev (: (⟨+⟩ $x $y) ⟨term⟩))))


---

(exec tpl-apply
  (, (ev (: $x ⟨term⟩))
     (ev (: $y ⟨term⟩)))
  (, (ev (: (⟨+⟩ $x $y) ⟨term⟩))))

; (= a b) : wff from a:term, b:term using weq
(exec weq-apply
  (, (ev (: $a ⟨term⟩))
     (ev (: $b ⟨term⟩)))
  (, (ev (: (⟨=⟩ $a $b) ⟨wff⟩))))

; Generic wim (implication constructor) rule
(exec wim-apply
  (, (ev (: $P ⟨wff⟩))
     (ev (: $Q ⟨wff⟩)))
  (, (ev (: (⟨->⟩ $P $Q) ⟨wff⟩))))

; ⊢ ((t+0) = t) via a2-curry @ t
(exec a2-instantiate-t
  (, (ev (: $a ⟨term⟩)))
  (, (ev (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩))))

(exec a1-instantiate-PtoQ
  (, (ev (: $a ⟨term⟩))
     (ev (: $bc ⟨term⟩)))
  (, (ev (: (⟨->⟩ (⟨=⟩ $a $bc)
               (⟨->⟩ (⟨=⟩ $a $bc)
                       (⟨=⟩ $bc $bc))) ⟨|-⟩))))

(exec derive-P-to-Q-direct3
  (, (ev (: $P ⟨wff⟩))
     (ev (: $IMP ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
     (ev (: (⟨->⟩ $P $IMP) ⟨|-⟩)))
  (, (ev (: $IMP ⟨|-⟩))))

; Final assembly using mp-curry (same single step as the working mm1)
; Inserting $P and $Q in appropriately.
; $P :- (⟨=⟩ (⟨+⟩ ⟨t⟩ ⟨0⟩) ⟨t⟩)
; $Q :- (⟨=⟩ ⟨t⟩ ⟨t⟩)
; Works now (with the P -> Q part)
(exec assemble-final-proof-direct
  (, (ev (: $P ⟨wff⟩))
     (ev (: $Q ⟨wff⟩))
     (ev (: $P ⟨|-⟩))
     (ev (: (⟨->⟩ $P $Q) ⟨|-⟩)))
  (, (ev (: $Q ⟨|-⟩))))

---

(kb (: ⟨a1⟩ (-> (: $a ⟨term⟩) (: $b ⟨term⟩) (: $c ⟨term⟩) (: (⟨->⟩ (⟨=⟩ $a $b) (⟨->⟩ (⟨=⟩ $a $c) (⟨=⟩ $b $c))) ⟨|-⟩))))


(exec a1-instantiate-PtoQ
  (, (ev (: $a ⟨term⟩))
     (ev (: $b ⟨term⟩))
     (ev (: $c ⟨term⟩)))
  (, (ev (: (⟨->⟩ (⟨=⟩ $a $b)
               (⟨->⟩ (⟨=⟩ $a $c)
                       (⟨=⟩ $b $c))) ⟨|-⟩))))    

                        (kb (: ⟨tpl⟩ (-> (: $x ⟨term⟩) (: $y ⟨term⟩) (: (⟨+⟩ $x $y) ⟨term⟩))))
  (kb (: ⟨weq⟩ (-> (: $x ⟨term⟩) (: $y ⟨term⟩) (: (⟨=⟩ $x $y) ⟨wff⟩))))
  (kb (: ⟨wim⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: (⟨->⟩ $P $Q) ⟨wff⟩))))

  ;; a1
  (exec (1 apply-equality-transitivity)
   (, (ev (: $a ⟨term⟩))
      (ev (: $b ⟨term⟩))
      (ev (: $c ⟨term⟩)))
   (, (ev (: (⟨->⟩ (⟨=⟩ $a $b)
               (⟨->⟩ (⟨=⟩ $a $c)
                       (⟨=⟩ $b $c))) ⟨|-⟩))))

  (exectrace (1 ⟨a1⟩) 
    (, (ev (: $a ⟨term⟩)) 
       (ev (: $b ⟨term⟩)) 
       (ev (: $c ⟨term⟩))) 
    (, (ev (: (⟨->⟩ (⟨=⟩ $a $b) 
                (⟨->⟩ (⟨=⟩ $a $c) 
                        (⟨=⟩ $b $c))) ⟨|-⟩))))

                          (exec (3 kp-mp 1)
    (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
    (, (ev (: $Q ⟨|-⟩))))


  (exec (3 kp-mp 1)
    (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
    (, (ev (: $Q ⟨|-⟩))))
  
    (exec (4 kp-mp 1)
    (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
    (, (ev (: $Q ⟨|-⟩))))

  (exec (3 kp-mp 2)
    (, (kb (: $name (-> (: $a $T1) (: $b $T2) (: $c $T3) (: $d $T4) (: $result $T5)))))
    (, (ev (: $result $T5))))

  (exec (4 kp-mp 2)
    (, (kb (: $name (-> (: $a $T1) (: $b $T2) (: $c $T3) (: $d $T4) (: $result $T5)))))
    (, (ev (: $result $T5))))

(exec (3 mp)
    (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
    (, (ev (: $Q ⟨|-⟩))))

  (exec (4 mp)
    (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩) (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))))
    (, (ev (: $Q ⟨|-⟩))))

 (step (1 abs))
      (, (goal (: $proof $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion)) ) ))

  ((step (2 rev))
    (, (ev (: $lhs (-> $a $r)))  (goal (: $k $r)) )
    (, (goal (: $rhs $a) ) ))

  ((step (3 abs2))
    (, (goal (: $proof $conclusion)))
    (, (goal (: $lhs (-> $syntha $synthb $conclusion)) ) ))

  ((step (4 rev2))
    (, (ev (: $lhs (-> $a $b $r)))  (goal (: $k $r)) )
    (, (goal (: $ap $a)) (goal (: $bp $b)) ))

  ((step (5 app))
    (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
    (, (ev (: (@ $lhs $rhs) $r) ) ))
    
  ((step (6 app2))
    (, (ev (: $f (-> $a $b $r)))  (ev (: $ap $a)) (ev (: $bp $b))  )
    (, (ev (: (@ $f $ap $bp) $r) ) ))

      ;; for tpl, weq, wim
  (exec (0 lift-binary-rule) 
  (, (kb (: $name (-> (: $x $T1) (: $y $T2) (: $result $T3)))))
  (, (exec (1 $name)
       (, (ev (: $x $T1) $D1) 
          (ev (: $y $T2) $D2))
       (, (ev (: $result $T3) ($D1 $D2 ($name $x $y)))))))

    ;; For ternary rules like a1
  (exec (0 lift-ternary-rule)
    (, (kb (: $name (-> (: $a $T1) (: $b $T2) (: $c $T3) (: $result $T4)))))
    (, (exec (2 $name)
        (, (ev (: $a $T1) $D1)
            (ev (: $b $T2) $D2)
            (ev (: $c $T3) $D3))
        (, (ev (: $result $T4) ($D1 $D2 $D3 ($name $D1 $D2 $D3)))))))

        (exec (3 mp)
    (, (, (kb (: ⟨mp⟩ (-> (: $P ⟨wff⟩) (: $Q ⟨wff⟩)
                        (: $P ⟨|-⟩) (: (⟨->⟩ $P $Q) ⟨|-⟩) (: $Q ⟨|-⟩)))) 
      (ev (: (⟨->⟩ $P $Q) ⟨|-⟩) $D4)
      (ev (: $P ⟨|-⟩) $D3)
      (ev (: $P ⟨wff⟩) $D1)
      (ev (: $Q ⟨wff⟩) $D2))
    (, (ev (: $Q ⟨|-⟩) ($D1 $D2 $D3 $D4 (⟨mp⟩ $P (⟨->⟩ $P $Q) )))))

      (kb (-> (: $a ⟨term⟩) (: (⟨=⟩ (⟨+⟩ $a ⟨0⟩) $a) ⟨|-⟩)))

      ((step (1 abs-curry))
      (, (goal (: $proof $conclusion)))
      (, 
        (goal (: $lhs (-> $synth $conclusion) )) 
        (debug $proof $conclusion made $lhs $synth $coclusion)))

         ((step (1 abs-curry2))
      (, (goal (: $proof $conclusion)))
      (, 
        (goal (: $lhs (-> $synth (: $proof $conclusion)) )) 
        (debug abs-curry2 (: $proof $conclusion) made (: $lhs (-> $synth (: $proof $conclusion))))))

        (exec 0 strip-name (, (kb (: $name $rule))) (, (ev rule)))
        (exec (0 lift) (, (kb (: $t $T))) (, (ev (: $t $T))))

(goal (: (⟨=⟩ ⟨t⟩ ⟨0⟩) ⟨wff⟩))

((step (2 rev2)) 
    (, (ev (: $a (-> $b $c $d))) 
       (goal $d))
    (, (goal $b)
       (goal $c) 
       (debug rev-cl (goal $d) made (goal $b) and (goal $c) due to (ev (: $a (-> $b $c $d))))))

  ((step (2 rev2-typed))
    (, (ev   (: $lhs (-> (: $arg1 $A) (: $arg2 $B) $R)))
      (goal (: $_   $R)))
    (, (goal (: $arg1 $A))
      (goal (: $arg2 $B))
      (debug rev2-typed need (: $arg1 $A) and (: $arg2 $B))))

  ((step (2 rev3-typed))
    (, (ev   (: $lhs (-> (: $arg1 $A) (: $arg2 $B) (: $arg3 $C) $R)))
      (goal (: $_   $R)))
    (, (goal (: $arg1 $A))
      (goal (: $arg2 $B))
      (goal (: $arg3 $C))
      (debug rev3-typed need args)))

((step (2 rev2)) 
    (, (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))) 
       (goal (: $d1 $d2))) 
    (, (goal (: $b1 $b2))
       (goal (: $c1 $c2)) 
       (debug rev2-cl (goal (: $d1 $d2)) )))

((step (2 rev2)) 
    (, (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))) 
       (goal (: $d1 $d2))) 
    (, (goal (: $b1 $b2))
       (goal (: $c1 $c2)) ))

       ((step (2 rev2)) 
    (, (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))) 
       (goal (: $d1 $d2))) 
    (, (goal (: $b1 $b2))
       (goal (: $c1 $c2)) 
       (debug rev2.0-cl (goal (: $d1 $d2)) made (goal (: $b1 $b2)) due to (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))) )))

       ( goal (: (⟨=⟩ ⟨t⟩ ⟨t⟩) ⟨|-⟩))

       ((step (2 rev2))
  (, (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2))))
     (goal (: $d1 $d2)))
  (, (goal (: $b1 $b2))
     (goal (: $c1 $c2))
     ; Generate a completion rule specific to this instantiation
     (exec (4 complete-$name-$b1-$c1)  ; Priority 4 - after base facts found
       (, (ev (: $b1 $b2)) 
          (ev (: $c1 $c2))
          (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))))
       (, (ev (: $d1 $d2))
          (debug completed $name for (: $d1 $d2))))
     (debug rev2.0-cl (goal (: $d1 $d2)) made (goal (: $b1 $b2)) due to (ev (: $name (-> (: $b1 $b2) (: $c1 $c2) (: $d1 $d2)))))))

      ((step (2 rev1))
    (, (ev (: $name (-> $a $b)))
      (goal $b))
    (, (goal $a)
      ; Generate completion rule for this specific instantiation
      (exec (4 app1)
        (, (ev $a)
            (ev (: $name (-> $a $b))))
        (, (ev $b)
            (debug completed ($name $a) for $b)))
      (debug rev-cl (goal $b) made (goal $a) due to (ev (: $name (-> $a $b))))))

       (exec (0 test-app2)
    (, (ev (: $f (-> $a $b)))
      (ev (: $x $a)))
    (, (ev ($f $x))))

      ((step (2 rev4))
    (, (ev (: $name (-> (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) (: $result $Tr))))
      (goal (: $result $Tr)))
    (, (goal (: $a $Ta))
      (goal (: $b $Tb))
      (goal (: $c $Tc))
      (goal (: $d $Td))
      ; Generate completion rule
      (exec (4 app4)
        (, (ev (: $a $Ta))
            (ev (: $b $Tb))
            (ev (: $c $Tc))
            (ev (: $d $Td))
            (ev (: $name (-> (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) (: $result $Tr)))))
        (, (ev (: $result $Tr))
            (debug completed ($name (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td)) for (: $result $Tr))))
      (debug rev4 (goal (: $result $Tr)) made goals (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) due to (ev (: $name (-> (: $a $Ta) (: $b $Tb) (: $c $Tc) (: $d $Td) (: $result $Tr)))))))

        ((step (3 mp))
    (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (ev (: $P ⟨|-⟩))
      (ev (: $P ⟨wff⟩))
      (ev (: $Q ⟨wff⟩)))
    (, (ev (: $Q ⟨|-⟩))))

  ((exec (4 mp))
    (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (ev (: $P ⟨|-⟩))
      (ev (: $P ⟨wff⟩))
      (ev (: $Q ⟨wff⟩)))
    (, (ev (: $Q ⟨|-⟩))))


    ((step (2 reflexivity-via-a1-a2))
    (, (goal (: (⟨=⟩ $x $x) ⟨|-⟩)))
    (, ; Use a2 to get x+0 = x, then use a1 with t=(x+0), r=x, s=x
      (goal (: $x ⟨term⟩))
      (goal (: (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) ⟨|-⟩))
      (goal (: (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨=⟩ $x $x))) ⟨|-⟩))
      ; Generate forward rule for final MP steps
      (exec (01 reflexivity-complete)
        (, (ev (: $x ⟨term⟩))
            (ev (: (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) ⟨|-⟩))
            (ev (: (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) ⟨wff⟩))
            (ev (: (⟨=⟩ $x $x) ⟨wff⟩))
            (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨=⟩ $x $x))) ⟨|-⟩)))
        (, ; First MP: P -> (P -> Q), P |- (P -> Q)
            (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨=⟩ $x $x)) ⟨|-⟩))
            (debug reflexivity first-mp done)))
      (exec (02 reflexivity-final)
        (, (ev (: (⟨->⟩ (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) (⟨=⟩ $x $x)) ⟨|-⟩))
            (ev (: (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) ⟨|-⟩))
            (ev (: (⟨=⟩ (⟨+⟩ $x ⟨0⟩) $x) ⟨wff⟩))
            (ev (: (⟨=⟩ $x $x) ⟨wff⟩)))
        (, ; Second MP: P -> Q, P |- Q
            (ev (: (⟨=⟩ $x $x) ⟨|-⟩))
            (debug reflexivity second-mp done)))))

            ((step (2 mp-contract))
    (, (goal (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (ev   (: $P ⟨|-⟩))
      (ev   (: (⟨->⟩ $P (⟨->⟩ $P $Q)) ⟨|-⟩))
      (ev   (: $P ⟨wff⟩))
      (ev   (: $Q ⟨wff⟩)))
    (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (debug completed mp-contract for (: (⟨->⟩ $P $Q) ⟨|-⟩))))


      ; Record HAVEs as soon as they appear (fires once per item)
((step (0 have))
  (, (need (: $x $T)) (ev (: $x $T)))
  (O (+ (have (: $x $T))) (- (need (: $x $T)))))

    ((step (05a mp1))
    (, (ev (: $name
              (-> (: $P ⟨wff⟩) (: (⟨->⟩ $P $Q) ⟨wff⟩)
                  (: $P ⟨|-⟩)
                  (: (⟨->⟩ $P (⟨->⟩ $P $Q)) ⟨|-⟩)
                  (: (⟨->⟩ $P $Q) ⟨|-⟩))))
      (ev (: $P ⟨|-⟩))
      (ev (: (⟨->⟩ $P (⟨->⟩ $P $Q)) ⟨|-⟩))
      (goal (: (⟨->⟩ $P $Q) ⟨|-⟩)))
    (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (debug mp1 built (: (⟨->⟩ $P $Q) ⟨|-⟩))))

       ((step (04 mp-contraction))
    (, (goal (: (⟨->⟩ $P $Q) ⟨|-⟩))
      (ev (: $P ⟨|-⟩))
      (ev (: (⟨->⟩ $P (⟨->⟩ $P $Q)) ⟨|-⟩)))
    (, (goal (: $P ⟨wff⟩))
      (goal (: $Q ⟨wff⟩))
      (exec (040 complete-mp-contraction)
        (, (ev (: $P ⟨wff⟩))
            (ev (: $Q ⟨wff⟩))
            (ev (: $P ⟨|-⟩))
            (ev (: (⟨->⟩ $P (⟨->⟩ $P $Q)) ⟨|-⟩)))
        (, (ev (: (⟨->⟩ $P $Q) ⟨|-⟩))
            (debug mp-contraction completed (⟨->⟩ $P $Q))))
      (debug mp-contraction trying to prove (⟨->⟩ $P $Q))))

         ((step (09 abstract-curry))
    (, (goal (: $proof $conclusion)))
    (, (goal (: $lhs (-> $synth (: $proof $conclusion))))
       (debug abstract-curry created (goal (: $lhs (-> $synth (: $proof $conclusion)))) for (: $proof $conclusion))))

       (exec 0 (, (wasm add $f)) (,
    (exec 1 (, (xs $i $x) (ys $i $y))
            (O (wasm $f ($x $y))
               (debug $x $y)))))

               (exec 0 (, (wasm add $f)) (,
    (exec 1 (, (xs $i $x) (ys $i $y))
            (O (+ (wasm $f ($x $y)))
               (+ (debug $x $y))))))