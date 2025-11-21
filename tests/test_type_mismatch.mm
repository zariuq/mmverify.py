$( Test: Type mismatch error
   metamath-knife output:
   error: Wrong floating typecode
   Step used for $f hypothesis does not match typecode
$)

$c term wff |- 0 ( ) -> $.
$v t r P Q $.

$( Type declarations $)
tt $f term t $.
tr $f term r $.
wp $f wff P $.
wq $f wff Q $.

$( 0 is a term $)
tze $a term 0 $.

$( implication requires two wffs $)
wim $a wff ( P -> Q ) $.

$( BAD PROOF: wim expects [wff, wff] but tze gives term $)
$( Stack after "tze tze": [(term 0), (term 0)] $)
$( wim needs: [(wff P), (wff Q)] - TYPECODE MISMATCH $)
bad $p wff ( 0 -> 0 ) $= tze tze wim $.
