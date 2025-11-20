$c wff pair $.
$v ph ps ch th $.

vph $f wff ph $.
vps $f wff ps $.
vch $f wff ch $.
vth $f wff th $.

$( Explicit declaration that ch and th are distinct $)
$d ch th $.

${
  $d ph ps $.
  ax-pair $a wff pair ph ps $.
$}

$( Test 2: Different variables with explicit DV - should PASS $)
test2_good $p wff pair ch th $=
  vch vth ax-pair
$.
