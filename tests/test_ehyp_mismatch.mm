$( Test: Essential hypothesis mismatch error
   For mp: fhyps=[wff P, wff Q], ehyps=[|- P, |- (P -> Q)]

   When using an axiom like ax-p $a |- P, we must also provide
   its floating hypothesis wp before calling it.

   Proof order for mp: wp wq <proof of |-P> <proof of |-(P->Q)> mp
   Where <proof of |-P> = wp ax-p (provide wp for ax-p's P variable)

   metamath-knife error: Essential hypothesis does not match proof step
$)

$c wff |- ( ) -> $.
$v P Q $.

wp $f wff P $.
wq $f wff Q $.

wim $a wff ( P -> Q ) $.

$( Axioms - each uses P and/or Q which need floating hyps $)
ax-p $a |- P $.
ax-q $a |- Q $.
ax-pq $a |- ( P -> Q ) $.
ax-qp $a |- ( Q -> P ) $.

$( Modus ponens $)
${
  min $e |- P $.
  maj $e |- ( P -> Q ) $.
  mp $a |- Q $.
$}

$( GOOD: Stack trace:
   wp wq -> [wff P, wff Q] (for mp's fhyps)
   wp -> [wff P, wff Q, wff P] (for ax-p)
   ax-p -> [wff P, wff Q, |- P]
   wp wq -> [wff P, wff Q, |- P, wff P, wff Q] (for ax-pq)
   ax-pq -> [wff P, wff Q, |- P, |- (P -> Q)]
   mp -> [|- Q]
$)
good $p |- Q $= wp wq wp ax-p wp wq ax-pq mp $.

$( BAD: Same structure but wrong axiom for ehyp
   wp wq -> [wff P, wff Q]
   wq -> [wff P, wff Q, wff Q] (for ax-q)
   ax-q -> [wff P, wff Q, |- Q] <-- WRONG! min expects |- P
   wp wq ax-pq -> [wff P, wff Q, |- Q, |- (P -> Q)]
   mp -> ERROR: |- Q doesn't match min's |- P
$)
bad1 $p |- Q $= wp wq wq ax-q wp wq ax-pq mp $.
