$( Test: Maybe we need explicit DV for the variables we substitute? $)

$c wff pair $.
$v ph ps ch th $.

vph  $f wff ph $.
vps  $f wff ps $.
vch  $f wff ch $.
vth  $f wff th $.

$( Declare that ch and th are distinct $)
$d ch th $.

$( Axiom with DV: ph and ps must be disjoint $)
${
  $d ph ps $.
  ax-pair $a wff pair ph ps $.
$}

$( Test 1: ph,ph - SHOULD FAIL $)
test1_bad $p wff pair ph ph $=
  vph vph ax-pair
$.

$( Test 2: ch,th where ch != th declared - SHOULD PASS $)
test2_good $p wff pair ch th $=
  vch vth ax-pair
$.
