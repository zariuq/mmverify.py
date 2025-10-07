$( Unit Test 43: Path canonicalization - same file via different paths $)
$( Should reject: False - both paths resolve to same file, second ignored $)
$( Spec: Canonical path comparison prevents duplicate processing $)

$c wff |- $.

$( First include - direct relative path $)
$[ ./test43_include_canonical_shared.mm $]

$( Second include - convoluted path to same file $)
$( ./subdir/../test43_include_canonical_shared.mm resolves to same file $)
$[ ./subdir/../test43_include_canonical_shared.mm $]

$( Use declarations - should work (file included once) $)
th1 $p |- var-canon $= fcanon ax-canon $.
