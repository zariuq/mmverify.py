$c wff nocnstr $.
$v ph $.

vph $f wff ph $.

$( Axiom with NO DV constraints $)
ax-no-dv $a wff nocnstr ph $.

$( Test 8: No constraints baseline - same variable is fine when no DV $)
test8_good $p wff nocnstr ph $=
  vph ax-no-dv
$.
