$c wff class = ( ) $.
$v ph ps x y z $.

vph $f wff ph $.
vps $f wff ps $.
vx $f class x $.
vy $f class y $.
vz $f class z $.

ax-eq $a wff ( x = y ) $.

${
  $d ph ps $.
  ax-pair $a wff ( ph ps ) $.
$}

$( Test 5: Nested expressions with overlap - x appears in both, violates DV $)
test5_bad $p wff ( ( x = y ) ( x = z ) ) $=
  vx vy ax-eq vx vz ax-eq ax-pair
$.
