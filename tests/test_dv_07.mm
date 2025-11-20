$c wff three $.
$v ph ps ch x y $.

vph $f wff ph $.
vps $f wff ps $.
vch $f wff ch $.
vx $f wff x $.
vy $f wff y $.

${
  $d ph ps $.
  $d ph ch $.
  $d ps ch $.
  ax-3way $a wff three ph ps ch $.
$}

$( Test 7: Three-way violation - x appears twice, violates ph != ps $)
test7_bad $p wff three x x y $=
  vx vx vy ax-3way
$.
