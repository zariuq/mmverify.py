$( Unit Test 38: Whitespace in valid compressed proof $)
$( Should reject: False - whitespace should be ignored per spec section 4.4.2 $)

$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.

$( Compressed proof with whitespace: spaces, newlines, tabs between valid steps $)
$( Proof is just: push wf (A), then ax (B) $)
$( Label list: [wf=0, ax=1], so A B is valid $)
th $p |- x $= ( ax )   A
  B   $.
