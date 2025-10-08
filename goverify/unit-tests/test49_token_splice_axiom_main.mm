$( Unit Test 49: Include as token splice in axiom $)
$( Should reject: True - Spec Section 4.1.2 forbids $[ ... $] inside statements $)
$( Attempting to splice tokens into an assertion must fail $)

$c wff |- $.
$v x $.
fx $f wff x $.

$( Include splices tokens into the middle of this statement $)
ax-splice $a $[ ./test49_token_splice_axiom_fragment.mm $]
