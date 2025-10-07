$( Unit Test 45: Variable redeclaration across scopes $)
$( Should reject: False - variable can be redeclared after scope ends $)
$( Spec Section 4.2.8: "A variable may be declared again after it becomes inactive" $)

$c wff class |- $.
$v x $.

${
  $( First scope: x has typecode wff $)
  fx1 $f wff x $.
  ax1 $a |- x $.
  $( Use x within its scope $)
  th1 $p |- x $= fx1 ax1 $.
$}

${
  $( Second scope: x has typecode class - VALID redeclaration $)
  fx2 $f class x $.
  ax2 $a class x $.
  $( Use x within its scope $)
  th2 $p class x $= fx2 ax2 $.
$}
