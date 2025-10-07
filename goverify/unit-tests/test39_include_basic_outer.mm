$( Unit Test 39: Basic include - outer file $)
$( Should reject: False - legitimate include should work $)

$( Include provides constants, variables, and axioms $)
$[ ./test39_include_basic_inner.mm $]

$( Use the included axiom to prove something $)
th1 $p |- ph $= wph ax-1 $.
