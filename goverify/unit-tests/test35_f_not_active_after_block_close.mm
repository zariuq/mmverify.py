$( Unit Test 35: $f not active after block close $)
$( Should reject: True $)

$c wff |- $.
${
  $v x $.
  wf $f wff x $.
$}
$( x and wf are no longer active $)
bad $a |- x $.
