$( Minimal DV test suite for metamath-knife - SIMPLIFIED
   Tests only variable-level DV constraints without building expressions $)

$c wff pair $.

$v ph ps ch th $.

vph  $f wff ph $.
vps  $f wff ps $.
vch  $f wff ch $.
vth  $f wff th $.

$( ===== Test 1: Direct collision - SHOULD FAIL ===== $)
$( DV constraint: ph != ps $)
$d ph ps $.
ax-pair $a wff pair ph ps $.

$( Proof: ax-pair(ph, ph) - same variable twice
   SHOULD FAIL with DV violation $)
test1_direct_bad $p wff pair ph ph $=
  vph vph ax-pair
$.

$( ===== Test 2: Different variables - SHOULD PASS ===== $)
$( Proof: ax-pair(ch, th) - different variables
   SHOULD PASS (no violation) $)
test2_different_good $p wff pair ch th $=
  vch vth ax-pair
$.

$( ===== Test 3: Symmetric violation - SHOULD FAIL ===== $)
$( Proof: ax-pair(ps, ps) - tests symmetry
   SHOULD FAIL (ph != ps implies ps != ph) $)
test3_symmetric_bad $p wff pair ps ps $=
  vps vps ax-pair
$.
