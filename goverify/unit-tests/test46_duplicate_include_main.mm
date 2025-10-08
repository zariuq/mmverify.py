$( Unit Test 46: Duplicate include at outermost scope $)
$( Should reject: False - second include is ignored per Spec Section 4.1.2 $)

$c wff |- $.

$( First include: processes the helper file $)
$[ ./test46_duplicate_include_helper.mm $]

$( Second include: must be ignored, avoiding duplicate declarations $)
$[ ./test46_duplicate_include_helper.mm $]

$( Use the declarations provided by the first include $)
th1 $p |- y $= wy ax-y $.
