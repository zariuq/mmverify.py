!(import! &self mmverify-utils_petta_partial)

!(println! "Setting up kb9...")
!(add-atom &self (kb9 (Constant "setvar" (Type "$c"))))
!(add_v "kb9" "x" 1)
!(add_v "kb9" "y" 1)
!(add_d "kb9" ("x" "y") 1)
!(println! "add_f result 1:")
!(println! (add_f "kb9" "vx" "setvar" "x" 1))
!(println! "add_f result 2:")
!(println! (add_f "kb9" "vy" "setvar" "y" 1))

!(println! "Checking what's in kb9 space:")
!(println! "VList atoms:")
!(matchc &self (kb9 (VList $depth $vlist)) (println! ("  VList" $depth $vlist)))

!(println! "DVar atoms:")
!(matchc &self (kb9 (DVar $vars $depth $type)) (println! ("  DVar" $vars $depth $type)))

!(println! "FList atoms:")
!(matchc &self (kb9 (FList $depth $flist)) (println! ("  FList" $depth $flist)))

!(println! "MandVar atoms:")
!(matchc &self (kb9 (MandVar $var)) (println! ("  MandVar" $var)))

!(println! "All kb9 atoms:")
!(match &self (kb9 $x) (println! ("  " $x)))
