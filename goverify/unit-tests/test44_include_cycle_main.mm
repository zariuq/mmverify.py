$( Unit Test 44: Cycle detection - A includes B, B includes A $)
$( Should reject: False - cycle should be detected and ignored $)
$( Spec: Include stack tracking prevents infinite loops $)

$c wff |- $.

$( Include A, which includes B, which tries to include A again $)
$[ ./test44_include_cycle_a.mm $]

$( Both A and B should be included exactly once $)
$( Use declarations from both files $)
th-a $p |- var-a $= fa-cycle ax-a-cycle $.
th-b $p |- var-b $= fb-cycle ax-b-cycle $.
