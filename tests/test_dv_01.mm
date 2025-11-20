$c wff pair $.
$v ph ps $.

vph $f wff ph $.
vps $f wff ps $.

${
  $d ph ps $.
  ax-pair $a wff pair ph ps $.
$}

$( Test 1: Direct collision - ph,ph violates $d ph ps $. $)
test1_bad $p wff pair ph ph $=
  vph vph ax-pair
$.
