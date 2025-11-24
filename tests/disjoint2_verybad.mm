$c formula |- ( ) $.

$v x y z w $.
xf $f formula x $.
yf $f formula y $.
zf $f formula z $.
wf $f formula w $.
combo $a formula ( x y ) $.
${
  $d x y $.
  ax-1 $a |- ( x y ) $.
$}

$( Should fail: uses z and x together, but ax-1 requires x,y disjoint
   and z is not declared disjoint from x $)
verybad $p |- ( ( x y ) ( z x ) ) $=
  xf yf combo zf xf combo ax-1 $.
