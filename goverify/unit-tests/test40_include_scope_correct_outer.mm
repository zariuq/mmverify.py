$( Unit Test 40: Include inside statement (forbidden) $)
$( Should reject: True - Spec Section 4.1.2 forbids $[ ... $] inside statements $)

$c wff |- $.
$v x $.
wx $f wff x $.
ax-x $a |- x $.

th-bad $p |- x $= $[ ./test40_include_scope_correct_inner.mm $] $.
