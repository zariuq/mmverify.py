$c wff |- $.
$v x $.
$d x x $.        $( INVALID: duplicates; must be two *different* variables $)
wx $f wff x $.

$(
  mmverify/adversarial_tests$ python3 mmverify.py -v 25 test_d_duplicate.mm 
mmverify.py -- Proof verifier for the Metamath language
Reading source file "test_d_duplicate.mm"...
Statement: ['wff', '|-']
Statement: ['x']
Statement: ['x', 'x']
Label: wx
Statement: ['wff', 'x']
No errors were found.
mmverify/adversarial_tests$ metamath test_d_duplicate.mm 
Metamath - Version 0.199.pre 29-Jan-2022      Type HELP for help, EXIT to exit.
MM> READ "test_d_duplicate.mm"
Reading source file "test_d_duplicate.mm"... 114 bytes
114 bytes were read into the source buffer.
The source has 4 statements; 0 are $a and 0 are $p.

?Error on line 3 of file "test_d_duplicate.mm" at statement 3, type "$d":
$d x x $.        
     ^
All variables in a "$d" statement must be unique.

One error was found.
$)