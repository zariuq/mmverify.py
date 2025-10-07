$( Unit Test 33: Compressed proof stack underflow $)
$( Should reject: True $)

$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( C tries to pop 3rd item, but stack has only 1 $)
bad $p |- x $= ( ax ) C $.
