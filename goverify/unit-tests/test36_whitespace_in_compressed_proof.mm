$( Unit Test 36: Whitespace in compressed proof $)
$( Should reject: False $)

$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( Whitespace inside compressed proof - should be ignored $)
th $p |- x $= ( ax ) A
  B
	C $.
