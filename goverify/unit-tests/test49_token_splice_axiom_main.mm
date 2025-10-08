$( Unit Test 49: Include as token splice in axiom $)
$( Should reject: False - token splice is valid macro expansion $)
$( Category: POLICY - Optional token splice $)
$( Spec Section 4.4.4: File includes are token splices, can appear anywhere $)
$( This is MALICIOUS but VALID per spec! $)

$c wff |- $.
$v x $.
fx $f wff x $.

$( Include splices tokens into the middle of this statement $)
ax-splice $a $[ ./test49_token_splice_axiom_fragment.mm $]
