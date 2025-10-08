$( Unit Test 50: Include as token splice in proof $)
$( Should reject: True - Spec Section 4.1.2 forbids $[ ... $] inside statements $)
$( Proof steps cannot be spliced from includes $)

$c wff |- $.
$v x $.
fx $f wff x $.
ax-x $a |- x $.

$( Include splices proof steps from external file $)
th $p |- x $= $[ ./test50_token_splice_proof_fragment.mm $] $.
