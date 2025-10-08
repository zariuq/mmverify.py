$( Unit Test 17: Include inside block (not outermost scope) $)
$( Should reject: True - Spec Section 4.1.2 forbids $[ ... $] between ${ and $} $)

$c wff |- $.
$v x $.
wx $f wff x $.

${
  $( Include is placed inside the block - this is illegal per spec $)
  $[ ./inner_test17.mm $]
$}
