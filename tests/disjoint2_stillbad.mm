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

$( Should fail: declares x,y,z disjoint but uses z and x together,
   and ax-1 only requires x,y disjoint $)
${
  $d x y z $.
  stillbad $p |- ( ( x y ) ( z x ) ) $=
    xf yf combo zf xf combo ax-1 $.
$}
