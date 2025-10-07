$( Unit Test 17: Include inside block (not outermost scope) $)
$( Should reject: True $)

$c wff $.
${
  $[ /tmp/inner.mm $]
  $v x $.
$}
