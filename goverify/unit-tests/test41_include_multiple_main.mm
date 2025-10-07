$( Unit Test 41: Multiple includes $)
$( Should reject: False - multiple includes should work $)

$c wff |- $.

$( Include file A $)
$[ ./test41_include_multiple_a.mm $]

$( Include file B $)
$[ ./test41_include_multiple_b.mm $]

$( Use content from both includes $)
th-a $p |- var-a $= fa ax-a $.
th-b $p |- var-b $= fb ax-b $.
