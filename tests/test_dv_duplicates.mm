$( Test file to verify metamath-knife behavior with duplicate variables in $d statements $)

$c |- wff $.
$v x y z ph ps $.

$( Test 1: Normal $d statement $)
${ test1.1 $e |- ph $.
   $d x y $.
   test1 $p |- ph $= test1.1 $.
$}

$( Test 2: Duplicate variable in $d - does metamath-knife accept this? $)
${ test2.1 $e |- ps $.
   $d x y z z $.
   test2 $p |- ps $= test2.1 $.
$}

$( Test 3: Same variable twice $)
${ test3.1 $e |- ph $.
   $d x x $.
   test3 $p |- ph $= test3.1 $.
$}

$( Test 4: Many duplicates $)
${ test4.1 $e |- ps $.
   $d x y x y z $.
   test4 $p |- ps $= test4.1 $.
$}
