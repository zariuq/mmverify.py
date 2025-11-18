; MeTTa version of add_d - Complete test suite
; Import all functions from mmverify-utils.metta

!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

!(bind! &kb1 (new-space))
!(add_d &kb1 (x y) 0)
!(assertEqual (match &kb1 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b)) (x y))

; Test 2: Reverse order should produce same ordered pair
!(bind! &kb2 (new-space))
!(add_d &kb2 (y x) 0)
!(assertEqual (match &kb2 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b)) (x y))

; Test 3: Three variables create three pairs
!(bind! &kb3 (new-space))
!(add_d &kb3 (x y z) 0)
!(assertEqualToResult (match &kb3 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b))
                      ((x y) (x z) (y z)))

; Test 4: Duplicate add should be idempotent (no duplicate entries)
!(bind! &kb4 (new-space))
!(add_d &kb4 (x y) 0)
!(add_d &kb4 (x y) 0)
!(add_d &kb4 (y x) 0)
!(assertEqual (match &kb4 (DVar ($a $b) (FSDepth 0) (Type "$d")) ($a $b)) (x y))

; Test 5: Different levels should create separate constraints
!(bind! &kb5 (new-space))
!(add_d &kb5 (x y) 0)
!(add_d &kb5 (x y) 1)
!(assertEqualToResult (match &kb5 (DVar (x y) (FSDepth $l) (Type "$d")) $l) (0 1))
