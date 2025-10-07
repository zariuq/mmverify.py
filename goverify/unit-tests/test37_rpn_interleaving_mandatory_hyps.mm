$( Unit Test 37: RPN interleaving of $f and $e in mandatory hypotheses $)
$( Should reject: False - This documents correct behavior $)

$c wff |- -> ( ) $.
$v ph ps $.

${
  $( $f for ph $)
  wph $f wff ph $.

  $( $e using ph $)
  h1 $e |- ph $.

  $( $f for ps - AFTER the $e (interleaved!) $)
  wps $f wff ps $.

  $( Assertion: mandatory hyps in RPN order MUST be: wph, h1, wps $)
  $( NOT: wph, wps, h1 (which would be "all $f then $e") $)
  ax-test $a |- ( ph -> ps ) $.
$}

$( This test documents the CORRECT mandatory hypothesis order. $)
$( A verifier that incorrectly orders as "all $f, then all $e" would get: $)
$(   WRONG: wph, wps, h1 $)
$( The correct order per spec is appearance order: $)
$(   CORRECT: wph, h1, wps $)

$( To verify: use metamath.exe "show statement ax-test /full" $)
$( Expected output: "Its mandatory hypotheses in RPN order are:" $)
$(   wph $f wff ph $. $)
$(   h1 $e |- ph $. $)
$(   wps $f wff ps $. $)
