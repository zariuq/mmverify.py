$( Unit Test 27: Disjoint variable constraint violation $)
$( Should reject: True $)

$c wff -> |- ( ) $.
$v x y z $.
wfx $f wff x $.
wfy $f wff y $.
wfz $f wff z $.
$d x y $.

$( Axiom mentions BOTH x and y, so $d x y is mandatory for it $)
axxy $a |- ( x -> y ) $.

$( This proof violates $d: substitutes z for both x and y $)
$( x:=z, y:=z violates $d x y $)
bad $p |- ( z -> z ) $= wfz wfz axxy $.
