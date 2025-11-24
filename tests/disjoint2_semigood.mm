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

$( Should fail: uses (x y) and (z w) but only x,y are declared disjoint by ax-1.
   Need to also declare x,z; x,w; y,z; y,w as disjoint $)
semigood $p |- ( ( x y ) ( z w ) ) $=
  xf yf combo zf wf combo ax-1 $.
