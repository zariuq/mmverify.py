$( Unit Test 44a: Cycle detection - file A $)

$c const-a $.
$v var-a $.
fa-cycle $f const-a var-a $.
ax-a-cycle $a |- var-a $.

$( Include B, which will try to include A back (cycle) $)
$[ ./test44_include_cycle_b.mm $]
