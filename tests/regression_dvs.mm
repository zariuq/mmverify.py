$( Regression test for DV checking $)
$c ( ) -> wff term |- = $.
$v x y z $.
vx $f term x $.
vy $f term y $.
vz $f term z $.
${
    $d x y $.
    ax-disjoint $a |- x = y $.
$}
${
    $( This proof should FAIL: using ax-disjoint requires $d x y,
       but we're substituting x for both, so x must be $d with itself - impossible $)
    verybad $p |- x = x $=
        vx vx ax-disjoint
    $.
$}
