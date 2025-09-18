$c wff |- -> $.  $( declare constants $) 
$v ph $.         $( one variable $)
$d -> ph $.      $( INVALID: '->' is a constant; $d must use variables only $)
wph $f wff ph $. $( make the file otherwise well-formed $)

$(
  mmverify/adversarial_tests$ python3 mmverify.py test_d_constant.mm -v 25
mmverify.py -- Proof verifier for the Metamath language
Reading source file "test_d_constant.mm"...
Statement: ['wff', '|-', '->']
Statement: ['ph']
Statement: ['->', 'ph']
Label: wph
Statement: ['wff', 'ph']
No errors were found.
mmverify/adversarial_tests$ metamath test_d_constant.mm 
Metamath - Version 0.199.pre 29-Jan-2022      Type HELP for help, EXIT to exit.
MM> READ "test_d_constant.mm"
?Warning: the last line in file "test_d_constant.mm" is incomplete.
Reading source file "test_d_constant.mm"... 216 bytes
216 bytes were read into the source buffer.
The source has 4 statements; 0 are $a and 0 are $p.

?Error on line 3 of file "test_d_constant.mm" at statement 3, type "$d":
$d -> ph $.     
   ^^
Constant symbols are not allowed in a "$d" statement.

One error was found.
$)