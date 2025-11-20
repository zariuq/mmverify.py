$c wff class = ( ) $.
$v ph ps x y z w $.

vph $f wff ph $.
vps $f wff ps $.
vx $f class x $.
vy $f class y $.
vz $f class z $.
vw $f class w $.

$( Declare all pairs disjoint $)
$d x y $.
$d x z $.
$d x w $.
$d y z $.
$d y w $.
$d z w $.

ax-eq $a wff ( x = y ) $.

${
  $d ph ps $.
  ax-pair $a wff ( ph ps ) $.
$}

$( Test 4: Nested expressions with disjoint sets - should PASS $)
test4_good $p wff ( ( x = y ) ( z = w ) ) $=
  vx vy ax-eq vz vw ax-eq ax-pair
$.
