; Debug test for matchc

!(import! &self ../mmverify-utils_petta)

!(println! "=== Debugging matchc ===")

; Add atom with kb2 tag
!(add-atom &self (kb2 (Color red)))

; Check what's in &self
!(println! "Atoms in &self with kb2 tag:")
!(println! (match &self (kb2 $x) $x))

; Try collapse
!(println! "After collapse:")
!(println! (collapse (match &self (kb2 $x) $x)))

; Try the specific pattern
!(println! "Matching (kb2 (Color $x)):")
!(println! (match &self (kb2 (Color $x)) $x))

; After collapse
!(println! "After collapse:")
!(println! (collapse (match &self (kb2 (Color $x)) $x)))

; Test matchc directly
!(println! "Using matchc:")
!(println! (matchc &self (kb2 (Color $x)) $x))
