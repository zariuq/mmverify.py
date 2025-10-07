$( Unit Test 27: Disjoint variable constraint violation $)
$( Should reject: True $)

$c wff |- $.
$v x y $.
wfx $f wff x $.
wfy $f wff y $.
$d x y $.
ax $a |- x $.
$( Proof violates $d: both x and y map to x $)
bad $p |- y $= wfy ax $.
