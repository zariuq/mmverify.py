$c wff four ( ) $.
$v ph ps ch th x y z $.

vph $f wff ph $.
vps $f wff ps $.
vch $f wff ch $.
vth $f wff th $.
vx $f wff x $.
vy $f wff y $.
vz $f wff z $.

${
  $d ph ps $.
  $d ph ch $.
  $d ph th $.
  $d ps ch $.
  $d ps th $.
  $d ch th $.
  ax-4way $a wff ( ph ps ch th ) $.
$}

$( Test 9: Four-way violation - x in positions 1 and 3, violates ph != ch $)
test9_bad $p wff ( x y x z ) $=
  vx vy vx vz ax-4way
$.
