$( Unit Test 50: Include as token splice in proof $)
$( Should reject: False - token splice is valid macro expansion $)
$( Category: POLICY - Optional token splice $)
$( Spec Section 4.4.4: File includes are token splices $)
$( This demonstrates proof steps can be in separate file $)

$c wff |- $.
$v x $.
fx $f wff x $.
ax-x $a |- x $.

$( Include splices proof steps from external file $)
th $p |- x $= $[ ./test50_token_splice_proof_fragment.mm $] $.
