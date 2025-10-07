$( Unit Test 47: $c declaration in inner scope via include $)
$( Should reject: True - $c must be in outermost block $)
$( Spec Section 4.2.8: "All $c statements must be placed in the outermost block" $)

$c wff |- $.

${
  $( Include file that contains $c declaration $)
  $( Since this include is in inner scope, $c is NOT in outermost block $)
  $[ ./test47_constant_inner_scope_helper.mm $]
$}
