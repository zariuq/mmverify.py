;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metta definitions helpful in transpiling mmverify.py into MeTTa     ;;
;;                                                                     ;;
;;                                                                     ;;
;;                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (apply_subst_tok $tok $subst)
  (case ((py-dot $subst get) $tok)
    ((() $tok) ;; If the token ($tok) is not in the substitution-binding dictionary ($subst), keep it as is.
    ($sub_tok $sub_tok)) ;; If the token ($tok) is in the dictionry ($subst), then return the substituted token ($sub_tok)
  ))

(= (apply_subst $stmt $subst)
  (map-atom $stmt $tok (apply_subst_tok $tok $subst)))