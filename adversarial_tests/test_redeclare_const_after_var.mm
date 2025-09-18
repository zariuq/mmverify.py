${ $v x $. $}    $( x is a variable only inside this block $)
$c x $.          $( INVALID: variable 'x' later redeclared as a constant $)

$(
mmverify/adversarial_tests$ python3 mmverify.py -v 25 test_redeclare_const_after_var.mm 
mmverify.py -- Proof verifier for the Metamath language
Reading source file "test_redeclare_const_after_var.mm"...
Statement: ['x']
Statement: ['x']
No errors were found.
mmverify/adversarial_tests$ metamath test_redeclare_const_after_var.mm 
Metamath - Version 0.199.pre 29-Jan-2022      Type HELP for help, EXIT to exit.
MM> READ "test_redeclare_const_after_var.mm"
?Warning: the last line in file "test_redeclare_const_after_var.mm" is incomple
te.
Reading source file "test_redeclare_const_after_var.mm"... 138 bytes
138 bytes were read into the source buffer.
The source has 4 statements; 0 are $a and 0 are $p.

?Error on line 1 of file "test_redeclare_const_after_var.mm" at statement 2,
type "$v":
${ $v x $. $}    
      ^
A symbol may not be both a constant and a variable.

?Error on line 2 of file "test_redeclare_const_after_var.mm" at statement 4,
type "$c":
$c x $.          
   ^
A symbol may not be both a constant and a variable.

2 errors were found.


$)