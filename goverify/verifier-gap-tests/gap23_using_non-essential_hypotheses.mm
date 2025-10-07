$( Gap 23: Using non-essential hypotheses $)
$( This database violates exactly ONE rule $)
$( Should reject: True $)

$c wff |- $.
$v x $.
wf $f wff x $.
${
  hyp $e |- x $.
  th1 $p |- x $= hyp $.
$}
evil $p |- x $= ( hyp ) A $.
