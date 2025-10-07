$( Unit Test 44b: Cycle detection - file B $)

$c const-b $.
$v var-b $.
fb-cycle $f const-b var-b $.
ax-b-cycle $a |- var-b $.

$( Try to include A back - creates cycle A->B->A $)
$( Per spec: this should be ignored (A already on stack) $)
$[ ./test44_include_cycle_a.mm $]
