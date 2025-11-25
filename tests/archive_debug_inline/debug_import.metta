; Debug: Test if import actually works
!(import! &self mmverify-utils)

!(println! "Testing add_d import...")
!(bind! &kb (new-space))
!(println! "Created space")
!(add_d &kb (x y) 0)
!(println! "Called add_d")
!(println! "Contents of space:")
!(match &kb $pattern $pattern)
