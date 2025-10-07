$( Unit Test 17: Include inside block with scope violation $)
$( Should reject: True $)

$c wff |- $.
$v x $.
wx $f wff x $.

${
  $( Include inside block - contents scoped to block $)
  $[ /tmp/inner_test17.mm $]

  $( This would work - using inside the block $)
  $( th1 $p |- y $= wy ax-inner $. $)
$}

$( Try to use ax-inner outside the block - SCOPE VIOLATION $)
th2 $p |- y $= wy ax-inner $.
