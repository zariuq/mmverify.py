$( Unit Test 46: Duplicate include in different scopes $)
$( Should reject: False - second include is ignored per spec Section 4.4.4 $)
$( Spec: "only the first reference to this common file will be read in" $)

$c wff |- $.

${
  $( First include: processes the file $)
  $[ ./test46_duplicate_include_helper.mm $]

  $( Use the included content $)
  th1 $p |- y $= wy ax-y $.
$}

${
  $( Second include: should be ignored as whitespace $)
  $[ ./test46_duplicate_include_helper.mm $]

  $( This would fail if file processed twice (y redeclared) $)
  $( But since second include ignored, ax-y and wy are still available globally $)
  th2 $p |- y $= wy ax-y $.
$}
