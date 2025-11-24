!(println! "Testing match with kb name as string parameter")

!(add-atom &self (kb9 (Constant "setvar" (Type "$c"))))

!(println! "Test 1: Direct atom kb9:")
!(println! (collapse (match &self (kb9 (Constant $tc (Type "$c"))) found)))

!(println! "Test 2: Using string variable $kb = \"kb9\":")
!(let $kb "kb9"
  (println! (collapse (match &self ($kb (Constant $tc (Type "$c"))) found))))

!(println! "Test 3: What about literal string in pattern:")
!(println! (collapse (match &self ("kb9" (Constant $tc (Type "$c"))) found)))
