; Test file for matchc function
; matchc: collapse + match for querying spaces

; Test helper - wrapper around assertEqual for clearer test syntax
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (test $actual $expected) (assertEqual $actual $expected))

; Function under test
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

(= (matchc $space $pattern $query) (collapse (match $space $pattern $query)))

!(println! "=== Testing matchc ===")
!(println! "")

!(println! "Test 1: matchc on empty space returns ()")
!(bind! &kb1 (new-space))
!(assertEqual (matchc &kb1 (Foo $x) $x) ())

!(println! "Test 2: matchc finds single matching atom")
!(bind! &kb2 (new-space))
!(add-atom &kb2 (Color red))
!(assertEqual (matchc &kb2 (Color $x) $x) (red))

!(println! "Test 3: matchc finds multiple matching atoms (returns tuple)")
!(bind! &kb3 (new-space))
!(add-atom &kb3 (Number 1))
!(add-atom &kb3 (Number 2))
!(add-atom &kb3 (Number 3))
; matchc returns (1 2 3) as a tuple, not separate results
!(test (matchc &kb3 (Number $x) $x) (1 2 3))

!(println! "Test 4: matchc with complex pattern (returns tuple of tuples)")
!(bind! &kb4 (new-space))
!(add-atom &kb4 (Var x 0 (Type "$v")))
!(add-atom &kb4 (Var y 1 (Type "$v")))
; matchc returns ((x 0) (y 1)) as a tuple
!(test (matchc &kb4 (Var $name $level (Type "$v")) ($name $level))
       ((x 0) (y 1)))

!(println! "Test 5: matchc returns () when no match")
!(bind! &kb5 (new-space))
!(add-atom &kb5 (Foo bar))
!(assertEqual (matchc &kb5 (Baz $x) $x) ())

!(println! "")
!(println! "=== All matchc tests complete ===")
