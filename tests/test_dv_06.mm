$c wff three $.
$v ph ps ch th ta et $.

vph $f wff ph $.
vps $f wff ps $.
vch $f wff ch $.
vth $f wff th $.
vta $f wff ta $.
vet $f wff et $.

$( Declare all pairs disjoint $)
$d th ta $.
$d th et $.
$d ta et $.

${
  $d ph ps $.
  $d ph ch $.
  $d ps ch $.
  ax-3way $a wff three ph ps ch $.
$}

$( Test 6: Three-way satisfied - all pairs declared disjoint $)
test6_good $p wff three th ta et $=
  vth vta vet ax-3way
$.
