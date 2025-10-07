$( Unit Test 48: Include causing variable redeclaration conflict $)
$( Should reject: True - x already active when include tries to redeclare it $)
$( Spec Section 4.2.8: "A variable may not be declared a second time while it is active" $)

$c wff |- $.
$v x $.
fx $f wff x $.

$( Include file that also declares $v x - should fail $)
$[ ./test48_variable_conflict_helper.mm $]
