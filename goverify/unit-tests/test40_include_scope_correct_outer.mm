$( Unit Test 40: Include inside block - correct usage $)
$( Should reject: False - using included content inside block is valid $)

$c wff |- $.
$v x $.
wx $f wff x $.
ax-x $a |- x $.

${
  $( Include inside block $)
  $[ ./test40_include_scope_correct_inner.mm $]

  $( Use included axiom INSIDE the block - this should work $)
  th1 $p |- y $= wy ax-inner $.
$}

$( Outside the block, only x is available $)
th2 $p |- x $= wx ax-x $.
