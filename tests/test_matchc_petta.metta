; Test file for matchc function (PeTTa version)
; matchc: collapse + match for querying spaces
;
; PeTTa KEY DIFFERENCE: Instead of new-space + bind!, we use TAGS in &self
; Example: !(add-atom &self (kb1 (Color red))) instead of !(bind! &kb1 (new-space))

; Import all functions from mmverify-utils_petta.metta
!(import! &self ../mmverify-utils_petta)

; PeTTa test helper - uses PeTTa's built-in test function
; Note: In PeTTa, test returns 'true' on success, not [()]

!(println! "=== Testing matchc (PeTTa version) ===")
!(println! "")

!(println! "Test 1: matchc on empty space returns ()")
; PeTTa: kb1 is a TAG, not a space variable
!(test (matchc &self (kb1 (Foo $x)) $x) ())

!(println! "Test 2: matchc finds single matching atom")
; PeTTa: Add atom with kb2 tag
!(add-atom &self (kb2 (Color red)))
!(test (matchc &self (kb2 (Color $x)) $x) (red))

!(println! "Test 3: matchc finds multiple matching atoms (returns tuple)")
; PeTTa: Add atoms with kb3 tag
!(add-atom &self (kb3 (Number 1)))
!(add-atom &self (kb3 (Number 2)))
!(add-atom &self (kb3 (Number 3)))
; matchc returns (1 2 3) as a tuple, not separate results
!(test (matchc &self (kb3 (Number $x)) $x) (1 2 3))

!(println! "Test 4: matchc with complex pattern (returns tuple of tuples)")
; PeTTa: Add atoms with kb4 tag
!(add-atom &self (kb4 (Var x 0 (Type "$v"))))
!(add-atom &self (kb4 (Var y 1 (Type "$v"))))
; matchc returns ((x 0) (y 1)) as a tuple
!(test (matchc &self (kb4 (Var $name $level (Type "$v"))) ($name $level))
       ((x 0) (y 1)))

!(println! "Test 5: matchc returns () when no match")
; PeTTa: Add atom with kb5 tag
!(add-atom &self (kb5 (Foo bar)))
!(test (matchc &self (kb5 (Baz $x)) $x) ())

!(println! "")
!(println! "=== All matchc tests complete ===")
