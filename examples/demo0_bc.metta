!(bind! &md (new-space))
!(add-atom &md (: ⟨0⟩ Const))
!(add-atom &md (: ⟨+⟩ Const))
!(add-atom &md (: ⟨=⟩ Const))
!(add-atom &md (: ⟨->⟩ Const))
!(add-atom &md (: ⟨⟦⟩ Const))
!(add-atom &md (: ⟨⟧⟩ Const))
!(add-atom &md (: ⟨term⟩ Const))
!(add-atom &md (: ⟨wff⟩ Const))
!(add-atom &md (: ⟨|-⟩ Const))
!(add-atom &md (: ⟨t⟩ Var))
!(add-atom &md (: ⟨r⟩ Var))
!(add-atom &md (: ⟨s⟩ Var))
!(add-atom &md (: ⟨P⟩ Var))
!(add-atom &md (: ⟨Q⟩ Var))
!(add-atom &md (: tt (: ⟨t⟩ ⟨term⟩)))
!(add-atom &md (: tr (: ⟨r⟩ ⟨term⟩)))
!(add-atom &md (: ts (: ⟨s⟩ ⟨term⟩)))
!(add-atom &md (: wp (: ⟨P⟩ ⟨wff⟩)))
!(add-atom &md (: wq (: ⟨Q⟩ ⟨wff⟩)))
!(add-atom &md (: tze (: ⟨0⟩ ⟨term⟩)))
!(add-atom &md (: tpl (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨+⟩ $⟨r⟩ ) ⟨term⟩))))
!(add-atom &md (: weq (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨r⟩) ⟨wff⟩))))
!(add-atom &md (: wim (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨wff⟩))))
!(add-atom &md (: a1 (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: $⟨s⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨=⟩ $⟨r⟩ ⟨->⟩ ( $⟨t⟩ ⟨=⟩ $⟨s⟩ ⟨->⟩ $⟨r⟩ ⟨=⟩ $⟨s⟩ ) ) ⟨|-⟩))))
!(add-atom &md (: a2 (-> (: $⟨t⟩ ⟨term⟩) (: (( $⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ $⟨t⟩) ⟨|-⟩))))
!(add-atom &md (: mp (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: $⟨P⟩ ⟨|-⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨|-⟩) (: $⟨Q⟩ ⟨|-⟩))))
; !(add-atom &md (: th1 (-> (: $⟨t⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨t⟩) ⟨|-⟩))))

;; Curried versions are needed.
!(add-atom &md (: mp-curry
  (-> (: $P ⟨wff⟩)                    ; P is a wff
    (-> (: $Q ⟨wff⟩)                  ; Q is a wff  
      (-> (: $P ⟨|-⟩)                 ; P is provable
        (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩)     ; (P -> Q) is provable
          (: $Q ⟨|-⟩)))))))           ; conclusion: Q is provable

!(add-atom &md (: a1-curry 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: ($t ⟨=⟩ $r ⟨->⟩ ($t ⟨=⟩ $s ⟨->⟩ $r ⟨=⟩ $s)) ⟨|-⟩))))))

!(add-atom &md (: a1-curry' 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: (($t ⟨=⟩ $r) ⟨->⟩ (($t ⟨=⟩ $s) ⟨->⟩ ($r ⟨=⟩ $s))) ⟨|-⟩))))))

;; The result of demo0.mm can be constructed.
; !(include metamath)
; !(match &md $d (println! $d))
; !(match &md $d (add-atom &self $d))
; > !(get-type (((a1-curry (tpl tt tze)) tt) tt))
; [(: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩ ⟨->⟩ ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩ ⟨->⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)]
; > !(get-type (((a1-curry' (tpl tt tze)) tt) tt))
; [(: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩))) ⟨|-⟩)]
; > !(get-type ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt)))
; [(: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)]
; > !(get-type ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))))
; [(: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)]
; > !(bc &self
;    Nil
;    (fromNumber 10)                   
;    (: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
; [(: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]
