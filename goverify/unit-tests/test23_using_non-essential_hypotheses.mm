$( Unit Test 23: Using non-essential hypotheses $)
$( Should reject: True $)

$c wff |- $.
$v x $.
wf $f wff x $.
${
  hyp $e |- x $.
  th1 $p |- x $= hyp $.
$}
evil $p |- x $= ( hyp ) A $.
