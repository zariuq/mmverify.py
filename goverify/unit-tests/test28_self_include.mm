$( Unit Test 28: Self-include $)
$( Should reject: False - Spec section 4.1.2 says "will simply be ignored" $)
$( Note: metamath.exe REJECTS (spec divergence), mmverify_pure.py ACCEPTS (spec-compliant) $)

$c wff $.

$( Include this file itself - causes duplicate declarations $)
$[ ./test28_self_include.mm $]
