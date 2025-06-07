$( This is the Metamath database hol.mm. $)

$( Metamath is a formal language and associated computer program for
   archiving, verifying, and studying mathematical proofs, created by Norman
   Dwight Megill (1950--2021).  For more information, visit
   https://us.metamath.org and
   https://github.com/metamath/set.mm, and feel free to ask questions at
   https://groups.google.com/g/metamath. $)

$( The database hol.mm was created by Mario Carneiro on 7-Oct-2014. $)


$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file for higher-order logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  https://creativecommons.org/publicdomain/zero/1.0/

Mario Carneiro - email: di.gama at gmail.com

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c var $.   $( Typecode for variables (syntax) $)
  $c type $.  $( Typecode for types (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c . $.     $( Separator $)
  $c |= $.    $( Context separator $)
  $c bool $.  $( Boolean type $)
  $c ind $.   $( 'Individual' type $)
  $c -> $.    $( Function type $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c , $.     $( Context comma $)
  $c \ $.     $( Lambda expression $)
  $c = $.     $( Equality term $)
  $c T. $.    $( Truth term $)
  $c [ $.     $( Infix operator $)
  $c ] $.     $( Infix operator $)

  $v al $.  $( Greek alpha $)
  $v be $.  $( Greek beta $)
  $v ga $.  $( Greek gamma $)
  $v de $.  $( Greek delta $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C F R S T $.  $( Term variables $)

  $( $j syntax 'var' 'type' 'term'; bound 'var'; $)

  $( Let variable ` al ` be a type. $)
  hal $f type al $.
  $( Let variable ` be ` be a type. $)
  hbe $f type be $.
  $( Let variable ` ga ` be a type. $)
  hga $f type ga $.
  $( Let variable ` de ` be a type. $)
  hde $f type de $.

  $( Let variable ` x ` be a var. $)
  vx $f var x $.
  $( Let variable ` y ` be a var. $)
  vy $f var y $.
  $( Let variable ` z ` be a var. $)
  vz $f var z $.
  $( Let variable ` f ` be a var. $)
  vf $f var f $.
  $( Let variable ` g ` be a var. $)
  vg $f var g $.
  $( Let variable ` p ` be a var. $)
  vp $f var p $.
  $( Let variable ` q ` be a var. $)
  vq $f var q $.

  $( Let variable ` A ` be a term. $)
  ta $f term A $.
  $( Let variable ` B ` be a term. $)
  tb $f term B $.
  $( Let variable ` C ` be a term. $)
  tc $f term C $.
  $( Let variable ` F ` be a term. $)
  tf $f term F $.
  $( Let variable ` R ` be a term. $)
  tr $f term R $.
  $( Let variable ` S ` be a term. $)
  ts $f term S $.
  $( Let variable ` T ` be a term. $)
  tt $f term T $.

  $( A var is a term. $)
  tv $a term x : al $.

  $( The type of all functions from type ` al ` to type ` be ` . $)
  ht $a type ( al -> be ) $.
  $( The type of booleans (true and false). $)
  hb $a type bool $.
  $( The type of individuals. $)
  hi $a type ind $.

  $( A combination (function application). $)
  kc $a term ( F T ) $.
  $( A lambda abstraction. $)
  kl $a term \ x : al . T $.
  $( The equality term. $)
  ke $a term = $.
  $( Truth term. $)
  kt $a term T. $.
  $( Infix operator. $)
  kbr $a term [ A F B ] $.
  $( Context operator. $)
  kct $a term ( A , B ) $.

  $c wff $.  $( Not used; for mmj2 compatibility $)

  $( $j syntax 'wff'; syntax '|-' as 'wff'; $)

  $( Internal axiom for mmj2 use. $)
  wffMMJ2 $a wff A |= B $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2t $a wff A : al $.

  ${
    idi.1 $e |- R |= A $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idi $p |- R |= A $=
      idi.1 $.
  $}

  ${
    idt.1 $e |- A : al $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idt $p |- A : al $=
      idt.1 $.
  $}

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-syl $a |- R |= T $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    syl $p |- R |= T $=
      tr ts tt ax-syl.1 ax-syl.2 ax-syl $.
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.
    $( Join common antecedents.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-jca $a |- R |= ( S , T ) $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    jca $p |- R |= ( S , T ) $=
      tr ts tt ax-jca.1 ax-jca.2 ax-jca $.
  $}

  ${
    syl2anc.1 $e |- R |= S $.
    syl2anc.2 $e |- R |= T $.
    syl2anc.3 $e |- ( S , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    syl2anc $p |- R |= A $=
      tr ts tt kct ta tr ts tt syl2anc.1 syl2anc.2 jca syl2anc.3 syl $.
  $}
  
