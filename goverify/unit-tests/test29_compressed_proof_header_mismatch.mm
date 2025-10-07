$( Unit Test 29: Compressed proof header mismatch $)
$( Should reject: True $)

$c wff |- $.
$v x $.
wf $f wff x $.
ax1 $a |- x $.
ax2 $a |- x $.
$( Header lists ax1 but proof uses ax2! $)
bad $p |- x $= ( ax1 ) B $.
