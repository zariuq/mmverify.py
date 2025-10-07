$( Unit Test 36: Whitespace in compressed proof $)
$( Should reject: True - This database has invalid proof steps B and C $)
$( Original intent was to test whitespace handling, but ABC is invalid $)

$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( Compressed proof ABC: A=0 (wf), B=1 (ax), C=2 (out of bounds!) $)
th $p |- x $= ( ax ) A
  B
	C $.
