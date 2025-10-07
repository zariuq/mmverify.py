$( Unit Test 22: Typecode mismatch in substitution $)
$( Should reject: True $)

$c wff class |- $.
$v x y $.
f1 $f wff x $.
f2 $f class y $.
ax $a |- x $.
bad $p |- y $= f2 ax $.
