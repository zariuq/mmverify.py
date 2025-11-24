;; Test 1: Uniqueness
!(println! "=== Test 1: Uniqueness ===")
!(let* 
   (($s1 (new-space))
    ($s2 (new-space))
    ($s3 (new-space)))
   (if (or (== $s1 $s2) (or (== $s2 $s3) (== $s1 $s3)))
       (println! (FAILED: Spaces are not unique $s1 $s2 $s3))
       (println! (PASSED: Spaces are unique $s1 $s2 $s3))))

;; Test 2: Isolation
!(println! "=== Test 2: Isolation ===")
!(let*
   (($s1 (new-space))
    ($s2 (new-space)))
   (let*
     (($_1 (add-atom $s1 (UniqueTo1)))
      ($_2 (add-atom $s2 (UniqueTo2)))
      ($r1 (collapse (match $s1 (UniqueTo1) found)))
      ($r2 (collapse (match $s2 (UniqueTo2) found)))
      ($r1_in_2 (collapse (match $s2 (UniqueTo1) found)))
      ($r2_in_1 (collapse (match $s1 (UniqueTo2) found)))
     )
     (if (and (== $r1 (found)) 
              (and (== $r2 (found))
                   (and (== $r1_in_2 ()) 
                        (== $r2_in_1 ()))))
         (println! (PASSED: Spaces are isolated))
         (println! (FAILED: Isolation check $r1 $r2 $r1_in_2 $r2_in_1)))))

;; Test 3: Shared Content & Removal
!(println! "=== Test 3: Shared Content & Removal ===")
!(let*
   (($s1 (new-space))
    ($s2 (new-space)))
   (let*
     (($_1 (add-atom $s1 (Shared)))
      ($_2 (add-atom $s2 (Shared)))
      ($_3 (remove-atom $s1 (Shared)))
      ($r1 (collapse (match $s1 (Shared) found)))
      ($r2 (collapse (match $s2 (Shared) found)))
     )
     (if (and (== $r1 ()) (== $r2 (found)))
         (println! (PASSED: Removal isolated))
         (println! (FAILED: Removal check $r1 $r2)))))

;; Test 4: Complex Structures
!(println! "=== Test 4: Complex Structures ===")
!(let $s1 (new-space)
   (let $_ (add-atom $s1 (implies (and A B) C))
     (let $res (collapse (match $s1 (implies $p C) $p))
       (let $_dbg (println! (TEST4_RES: $res))
         (if (== $res ((and A B)))
             (println! (PASSED: Complex structure match))
             (println! (FAILED: Structure match $res)))))))

;; Test 5: Variables (Renaming/Unification)
!(println! "=== Test 5: Variables ===")
!(let $s1 (new-space)
   (let $_ (add-atom $s1 (is-human $x))
     (let $res (collapse (match $s1 (is-human $y) found))
       (if (== $res (found))
           (println! (PASSED: Variable matching))
           (println! (FAILED: Variable matching $res))))))

;; Test 6: Spaces as Data (Nesting)
!(println! "=== Test 6: Spaces as Data (Nesting) ===")
!(let*
   (($outer (new-space))
    ($inner (new-space)))
   (let*
     (($_1 (add-atom $inner (SecretData)))
      ($_2 (add-atom $outer (container $inner)))
      ($retrieved_data 
         (let $inner_ref (match $outer (container $c) $c)
           (match $inner_ref (SecretData) FOUND_IT)))
     )
     (if (== $retrieved_data FOUND_IT)
         (println! (PASSED: Nested space retrieval works))
         (println! (FAILED: Nested retrieval $retrieved_data)))))

!(println! ("type of map-atom:" (get-type map-atom)))
!(help! map-atom)


;; Test 7: Transfer (Read from one, Write to another)
!(println! "=== Test 7: Transfer ===")
!(let*
   (($src (new-space))
    ($dst (new-space)))
   (let*
     (($_1 (add-atom $src (MoveMe)))
      ($matches (collapse (match $src $x $x)))
      ; ($_2 (map-atom (match $src $x $x) $atom (add-atom $dst $atom)))
      ($_12 (println! ("matches:" $matches)))
      ($_2 (map-atom $matches $atom (add-atom $dst $atom)))
      ($r_dst (collapse (match $dst (MoveMe) found)))
      ($r_src (collapse (match $src (MoveMe) found)))
     )
     (if (and (== $r_dst (found)) (== $r_src (found)))
         (println! (PASSED: Transfer (Copy) works))
         (println! (FAILED: Transfer $r_dst $r_src)))))
