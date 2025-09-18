$( A test to see whether the verifier manages unknown proof steps.  The theorem 'good' is taken from disjoint2.mm from https://github.com/metamath/metamath-exe/tree/master/tests $)

$c formula |- ( ) $.

$v x y z w ph $.
xf $f formula x $.
yf $f formula y $.
zf $f formula z $.
wf $f formula w $.
wph $f formula ph $.
combo $a formula ( x y ) $.
${
  $d x y $.
  ax-1 $a |- ( x y ) $.
$}

th $p |- ph $= ? $.   $( INCOMPLETE proof, allowed by spec section 4.4.6 $)

${
  $d x y z w $.
  good $p |- ( ( x y ) ( z w ) ) $=
    xf yf combo zf wf combo ax-1 $.
$}

$(
mmverify/adversarial_tests$ metamath test_unknown_step.mm 
Metamath - Version 0.199.pre 29-Jan-2022      Type HELP for help, EXIT to exit.
MM> READ "test_unknown_step.mm"
?Warning: the last line in file "test_unknown_step.mm" is incomplete.
Reading source file "test_unknown_step.mm"... 378 bytes
378 bytes were read into the source buffer.
The source has 17 statements; 2 are $a and 2 are $p.
No errors were found.  However, proofs were not checked.  Type VERIFY PROOF *
if you want to check them.
MM> verify proof *
0 10%  20%  30%  40%  50%  60%  70%  80%  90% 100%
..................................................
Warning: The following $p statement(s) were not proved:  th
MM> ^C
mmverify/adversarial_tests$ python3 mmverify.py -v 25 test_unknown_step.mm 
mmverify.py -- Proof verifier for the Metamath language
Reading source file "test_unknown_step.mm"...
Statement: ['formula', '|-', '(', ')']
Statement: ['x', 'y', 'z', 'w', 'ph']
Label: xf
Statement: ['formula', 'x']
Label: yf
Statement: ['formula', 'y']
Label: zf
Statement: ['formula', 'z']
Label: wf
Statement: ['formula', 'w']
Label: wph
Statement: ['formula', 'ph']
Label: combo
Statement: ['formula', '(', 'x', 'y', ')']
Make assertion: (set(), [('formula', 'x'), ('formula', 'y')], [], ['formula', '(', 'x', 'y', ')'])
Statement: ['x', 'y']
Label: ax-1
Statement: ['|-', '(', 'x', 'y', ')']
Make assertion: ({('x', 'y')}, [('formula', 'x'), ('formula', 'y')], [], ['|-', '(', 'x', 'y', ')'])
Label: th
Statement: ['|-', 'ph']
Statement: ['?']
Make assertion: (set(), [('formula', 'ph')], [], ['|-', 'ph'])
Verify: th
Traceback (most recent call last):
  File "/.../mmverify/adversarial_tests/mmverify.py", line 706, in <module>
    mm.read(Toks(db_file))
  File "/.../mmverify/adversarial_tests/mmverify.py", line 446, in read
    self.verify(f_hyps, e_hyps, conclusion, proof)
  File "/.../mmverify/adversarial_tests/mmverify.py", line 626, in verify
    stack = self.treat_normal_proof(proof)
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/.../mmverify/adversarial_tests/mmverify.py", line 543, in treat_normal_proof
    raise MMError(f"No statement information found for label {label}")
MMError: No statement information found for label ?
$)