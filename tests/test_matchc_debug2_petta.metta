; Debug test for matchc - check if there's a naming conflict

!(import! &self ../mmverify-utils_petta)

!(println! "=== Debugging matchc - naming conflict? ===")

; Add atom
!(add-atom &self (kb2 (Color red)))

; Test calling matchc directly with inline definition
!(println! "Inline matchc:")
!(println! (collapse (match &self (kb2 (Color $x)) $x)))

; Check if matchc is defined
!(println! "Type of matchc:")
!(println! (get-type matchc))

; Try using unify to check the definition
!(println! "Checking matchc definition:")
!(println! (match &self (= (matchc $sp $p $q) $body) $body))
