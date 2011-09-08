(** * Standard finite sets . Vladimir Voevodsky . Apr. - Sep. 2011 .

This file contains main constructions related to the standard finite sets defined as the initial intervals of [ nat ] and their properties . *)




(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)


Require Export hnat .
Require Export hSet . 


(* To up-steram files *)







(** ** Standard finite sets [ stn ] . *)



Definition stn ( n : nat ) := total2 ( fun m : nat => lth m n ) .
Definition stnpair ( n : nat ) := tpair ( fun m : nat => lth m n ) .
Definition stntonat ( n : nat ) : stn n -> nat := @pr21 _ _ .
Coercion stntonat : stn >-> nat .


Lemma isinclstntonat ( n : nat ) : isincl ( stntonat n ) .
Proof. intro .  apply isinclpr21 .  intro x .  apply ( pr22 ( lth x n ) ) .  Defined.

Lemma isdecinclstntonat ( n : nat ) : isdecincl ( stntonat n ) .
Proof. intro . apply isdecinclpr21 .  intro x .  apply isdecpropgth .  Defined . 

Lemma neghfiberstntonat ( n m : nat ) ( is : geh m n ) : neg ( hfiber ( stntonat n ) m ) .
Proof. intros . intro h . destruct h as [ j e ] .  destruct j as [ j is' ] .  simpl in e .  rewrite e in is' .  apply ( neglehgth _ _ is is' ) . Defined .

Lemma iscontrhfiberstntonat ( n m : nat ) ( is : lth m n ) : iscontr ( hfiber ( stntonat n ) m ) .
Proof. intros .  apply ( iscontrhfiberofincl ( stntonat n ) ( isinclstntonat n ) ( stnpair n m is ) ) .  Defined . 

Lemma isisolatedinstn { n : nat } ( x : stn n ) : isisolated _ x.
Proof. intros . apply ( isisolatedinclb ( stntonat n ) ( isinclstntonat n ) x ( isisolatedn x ) ) .  Defined. 

Corollary isdeceqstn ( n : nat ) : isdeceq (stn n).
Proof. intro.  unfold isdeceq. intros x x' . apply (isisolatedinstn x x' ). Defined.

Definition weqisolatedstntostn ( n : nat ) : weq ( isolated ( stn n ) ) ( stn n ) .
Proof . intro . apply weqpr21 . intro x .   apply iscontraprop1 .  apply ( isapropisisolated ) . set ( int := isdeceqstn n x  ) . assumption .  Defined . 


Corollary isasetstn ( n : nat ) : isaset ( stn n ) .
Proof. intro . apply ( isasetifdeceq _ ( isdeceqstn n ) ) . Defined . 

Definition lastelement ( n : nat ) : stn ( S n ) .
Proof. intro .   split with n .  apply ( gthsnn ( S n ) ) .  Defined . 

Definition stnmtostnn ( m n : nat ) (isleh: leh m n ) : stn m -> stn n := fun x : stn m => match x with tpair i is => stnpair _ i ( lthlehtrans i m n is isleh ) end .  




(** ** "Boundary" maps [ dni : stn n -> stn ( S n ) ] and their properties . *) 



Definition dni ( n : nat ) ( i : stn ( S n ) ) : stn n -> stn ( S n ) .
Proof. intros n i x .  destruct ( leb i x ) . apply ( stnpair ( S n ) ( S x ) ( pr22 x ) ) . apply ( stnpair ( S n ) x ( gthimplgths _ _ ( pr22 x ) ) ) .   Defined.  

Lemma dnicommsq ( n : nat ) ( i : stn ( S n ) ) : commsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) .
Proof. intros . intro x . unfold dni . unfold di . destruct ( leb i x ) .  simpl . apply idpath . simpl .  apply idpath . Defined . 

Theorem dnihfsq ( n : nat ) ( i : stn ( S n ) ) : hfsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) .
Proof. intros . apply ( ishfsqweqhfibersgtof' ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) ( dnicommsq _ _  ) ) . intro x . set ( int := boolchoice ( leb n x ) ) .  destruct int as [ l | g ] . 

assert ( is1 : neg ( hfiber ( stntonat ( S n ) ) ( di i x ) ) ) . apply neghfiberstntonat . unfold di . destruct i as [ i l' ] . destruct ( gthchoice _ _ l' ) as [ g' | e ] .  set ( int := gehgthtrans _ _ _ l g' ) .  simpl in int . simpl . rewrite ( gthimplgeh _ _ int ) .  assumption . set ( e' := invmaponpathsS _ _ e ) . assert  ( l'' : leh n x  ) . apply l .  rewrite e' in l .  simpl . rewrite l . assumption . apply ( isweqtoempty2 _ is1 ) .

assert ( is1 : iscontr ( hfiber ( stntonat n ) x ) ) . apply iscontrhfiberstntonat . assumption .
assert ( is2 : iscontr ( hfiber ( stntonat ( S n ) ) ( di i x )  ) ) .    apply iscontrhfiberstntonat . apply ( lehlthtrans _ ( S x ) ( S n ) ( lehdinsn i x ) g ) .  
apply isweqcontrcontr .  assumption . assumption . 

Defined . 



Lemma weqhfiberdnihfiberdi ( n : nat ) ( i j : stn ( S n ) ) : weq ( hfiber ( dni n i ) j ) ( hfiber ( di i ) j ) .
Proof.  intros . apply ( weqhfibersg'tof _ _ _ _ ( dnihfsq n i ) j ) . Defined .

Lemma neghfiberdni ( n : nat ) ( i : stn ( S n ) ) : neg ( hfiber ( dni n i ) i ) . 
Proof. intros . apply ( negf ( weqhfiberdnihfiberdi n i i ) ( neghfiberdi i ) ) . Defined .  

Lemma iscontrhfiberdni ( n : nat ) ( i j : stn ( S n ) ) ( ne : neg ( paths i j ) ) : iscontr ( hfiber ( dni n i ) j ) .
Proof . intros . set ( ne' := negf ( invmaponpathsincl _ ( isinclstntonat ( S n ) ) _ _ ) ne ) .  apply ( iscontrweqb ( weqhfiberdnihfiberdi n i j ) ( iscontrhfiberdi i j ne' ) ) .  Defined . 

Lemma isdecincldni ( n : nat ) ( i : stn ( S n ) ) : isdecincl ( dni n i ) .
Proof.  intros . intro j . destruct ( isdeceqstn _ i j ) . rewrite i0 .  apply ( isdecpropfromneg ( neghfiberdni n j ) ) . apply ( isdecpropfromiscontr ( iscontrhfiberdni _ _ _ e ) ) .  Defined . 
 
Lemma isincldni ( n : nat ) ( i : stn ( S n ) ) : isincl ( dni n i ) .
Proof. intros . apply ( isdecincltoisincl _  ( isdecincldni n i ) ) .  Defined . 






(** ** Weak equivalences between standard finite sets and constructions on these sets *)



(** *** The weak equivalence from [ stn n ] to the compl of a point [ j ] in [ stn ( S n ) ] defined by [ dni n j ] *)


Definition dnitocompl ( n : nat ) ( i : stn ( S n ) ) ( j : stn n ) : compl ( stn ( S n ) ) i .
Proof. intros . split with ( dni n i j ) .  intro e .  apply ( neghfiberdni n i ( hfiberpair _ j ( pathsinv0 e ) ) ) .  Defined .

Lemma isweqdnitocompl  ( n : nat ) ( i : stn ( S n ) ) : isweq ( dnitocompl n i ) .
Proof. intros . intro jni . destruct jni as [ j ni ] . set ( jni := complpair _ i j ni ) .  destruct ( boolchoice ( eqbnat i j ) ) .  set ( ni' := negf ( invmaponpathsincl _ ( isinclstntonat _ ) i j ) ni ) . destruct ( ni' ( eqhtopaths _ _  i0 ) ) .  set ( w := samehfibers ( dnitocompl n i )  _ ( isinclpr21compl _ i ) jni ) .   simpl in w . assert ( is : iscontr (hfiber (fun x : stn n => dni n i x) j) ) . apply iscontrhfiberdni .  assumption . apply ( iscontrweqb w is ) .  Defined . 


Definition weqdnicompl ( n : nat ) ( i : stn ( S n ) ) := weqpair _ ( isweqdnitocompl n i ) . 




(** *** Weak equivalence from [ coprod ( stn n ) unit ] to [ stn ( S n ) ] defined by [ dni n i ] *)


Definition weqdnicoprod  ( n : nat ) ( j : stn ( S n ) ) : weq ( coprod ( stn n ) unit ) ( stn ( S n ) ) .
Proof . intros . apply ( weqcomp ( weqcoprodf ( weqdnicompl n j ) ( idweq unit ) ) ( weqrecompl ( stn ( S n ) ) j ( isdeceqstn ( S n ) j ) ) ) .  Defined . 




(** *** Weak equivalences from [ stn n ] for [ n = 0 , 1 , 2 ] to [ empty ] , [ unit ] and [ bool ] ( see also the section on [ nelstruct ] in finitesets.v ) . *)

Definition negstn0 : neg ( stn 0 ) .
Proof . intro x .  destruct x as [ a b ] .  simpl in b . apply nopathstruetofalse .  assumption .  Defined . 

Definition weqstn0toempty : weq ( stn 0 ) empty .
Proof .  apply weqtoempty . apply negstn0 . Defined .  

Definition weqstn1tounit : weq ( stn 1 ) unit .
Proof. set ( f := fun x : stn 1 => tt ) . apply weqcontrcontr .  split with ( lastelement 0 ) .   intro t .  destruct t as [ t l ] . set ( e := lth1implis0 _ l ) .   apply ( invmaponpathsincl _ ( isinclstntonat 1 ) ( stnpair _ t l ) ( lastelement 0 ) e ) .  apply iscontrunit .  Defined .

Corollary iscontrstn1 : iscontr ( stn 1 ) .
Proof. apply iscontrifweqtounit . apply weqstn1tounit . Defined . 

Lemma isinclfromstn1 { X : UU0 } ( f : stn 1 -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isasetstn 1 ) is ) . intros x x' e . apply ( invmaponpathsweq weqstn1tounit x x' ( idpath tt ) )  .  Defined .    

Definition weqstn2tobool : weq ( stn 2 ) bool .
Proof. set ( f := fun j : stn 2 => if eqbnat j 0 then false else true ) .  set ( g := fun b : bool => match b with false => stnpair 2 0 ( idpath false ) | true => stnpair 2 1 ( idpath false ) end ) .  split with f . 
assert ( egf : forall j : _ , paths ( g ( f j ) ) j ) . intro j . unfold f . destruct ( boolchoice ( eqbnat j 0 ) ) as [ e | ne ] .   rewrite e .   simpl . apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . rewrite ( eqhtopaths j 0 e ) .  apply idpath . rewrite ne . simpl .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . destruct j as [ j l ] . simpl .  destruct ( gthchoice _ _ l ) as [ h | i ] . destruct ( neqhtonegpaths _ _ ne ( lth1implis0 _ h ) ) .  apply ( invmaponpathsS _ _ i ) .  
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  unfold g .  destruct b . apply idpath . apply idpath. 
apply ( gradth _ _ egf efg ) . Defined . 






(** ***  Weak equivalence between the coproduct of [ stn n ] and [ stn m ] and [ stn ( n + m ) ] *)

Theorem weqfromcoprodofstn ( n m : nat ) : weq ( coprod ( stn n ) ( stn m ) ) ( stn ( n + m ) ) .
Proof. intros . 

assert ( i1 : forall i : nat , lth i n -> lth i ( n + m ) ) . intros i1 l . apply ( lthlehtrans _ _ _ l ( lehnplusnm n m ) ) .    
assert ( i2 : forall i : nat , lth i m -> lth ( i + n ) ( n + m ) ) .  intros i2 l .  rewrite ( natpluscomm i2  n ) .  apply gthandplusl . assumption . 
set ( f := fun ab : coprod ( stn n ) ( stn m ) => match ab with ii1 a =>  stnpair ( n + m ) a ( i1 a ( pr22 a ) ) | ii2 b => stnpair ( n + m ) ( b + n ) ( i2 b ( pr22 b ) ) end ) . 
split with f . 

assert ( is : isincl f ) .  apply  isinclbetweensets . apply ( isofhlevelssncoprod 0 _ _ ( isasetstn n ) ( isasetstn m ) ) .  apply ( isasetstn ( n + m ) ) .  intros x x' . intro e .   destruct x as [ xn | xm ] .

destruct x' as [ xn' | xm' ] . apply ( maponpaths (@ii1 _ _ ) ) .  apply ( invmaponpathsincl _ ( isinclstntonat n ) _ _ ) .  destruct xn as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  simpl .  apply ( maponpaths ( stntonat ( n + m ) ) e  )  .   destruct xn as [ x ex ] . destruct xm' as [ x' ex' ] . simpl in e . assert ( l : leh n x ) . set ( e' := maponpaths ( stntonat _ ) e ) .   simpl in e' . rewrite e' .  apply ( lehmplusnm x' n  ) . destruct ( neglehgth _ _ l ex ) .  

destruct x' as [ xn' | xm' ] . destruct xm as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  assert ( e' := maponpaths ( stntonat _ ) e ) .  simpl in e' .  assert ( a : empty ) . clear e . rewrite ( pathsinv0 e' ) in ex' .  apply ( neggthmplusnm _ _ ex' )  .   destruct a . destruct xm as [ x ex ] . destruct xm' as [ x' ex' ] .  simpl in e .  apply ( maponpaths ( @ii2 _ _ ) ) .   simpl .  apply ( invmaponpathsincl _ ( isinclstntonat m ) _ _ ) .  simpl .  apply ( invmaponpathsincl _ ( isinclplusn n ) _ _ ( maponpaths ( stntonat _ ) e ) ) .  

intro jl . apply iscontraprop1 .  apply ( is jl ) .   destruct jl as [ j l ] . destruct ( boolchoice ( leb n j ) ) as [ ni | i ] .   set ( jmn := pr21 ( iscontrhfiberplusn n j ni ) ) .   destruct jmn as [ k e ] . assert ( is'' : lth k m ) . rewrite ( pathsinv0 e ) in l .  rewrite ( natpluscomm k n ) in l .  apply ( gthandpluslinv _ _ _ l ) . split with ( ii2 ( stnpair _ k is'' ) ) .  simpl .  apply ( invmaponpathsincl _ ( isinclstntonat _ ) (stnpair _ (k + n) (i2 k is'')) ( stnpair _ j l ) e ) . 

split with ( ii1 ( stnpair _ j i ) ) . simpl .   apply ( invmaponpathsincl _ ( isinclstntonat ( n + m ) )  (stnpair (n + m) j (i1 j i)) ( stnpair _ j l )  ( idpath j ) ) .
Defined .



(** *** Weak equivalence from the total space of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnsum n f ) ] *)

Definition stnsum { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 0 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) + f ( lastelement n ) ) . Defined . 

Theorem weqstnsum { n : nat } ( P : stn n -> UU0 ) ( f : stn n -> nat ) ( ww : forall i : stn n , weq ( stn ( f i ) )  ( P i ) ) : weq ( total2 P ) ( stn ( stnsum f ) ) .
Proof . intro n . induction n as [ | n IHn ] . intros . simpl .  apply weqtoempty2 .  apply ( @pr21 _ _ ) .  apply negstn0 . intros .  simpl .  set ( a := stnsum (fun i : stn n => f (dni n (lastelement n) i)) ) . set ( b :=  f (lastelement n) ) . set ( w1 := invweq ( weqfp ( weqdnicoprod n ( lastelement n ) ) P ) ) . set ( w2 := weqcomp w1 ( weqtotal2overcoprod (fun x : coprod (stn n) unit => P ( weqdnicoprod n ( lastelement n )  x)) ) ) .  simpl in w2 . assert ( w3 : weq (total2 (fun x : stn n => P (dni n (lastelement n) x))) ( stn a ) ) .  assert ( int : forall x : stn n , weq  ( stn ( f ( dni n (lastelement n) x) ) ) ( P (dni n (lastelement n) x) ) ) .  intro x . apply ( ww ( dni n (lastelement n) x) ) .  apply ( IHn ( fun x : stn n => P (dni n (lastelement n) x)) ( fun x : stn n => f ( dni n (lastelement n) x ) ) int ) .  assert ( w4 : weq (total2 (fun _ : unit => P (lastelement n))) ( stn b) ) . apply ( weqcomp ( weqtotal2overunit (fun _ : unit => P (lastelement n)) ) ( invweq ( ww ( lastelement n ) ) ) ) .   apply ( weqcomp w2 ( weqcomp ( weqcoprodf w3 w4 ) ( weqfromcoprodofstn a b ) ) ) .  Defined . 


Corollary weqstnsum2 { X : UU0 } ( n : nat ) ( f : stn n -> nat ) ( g : X -> stn n ) ( ww : forall i : stn n , weq ( stn ( f i ) ) ( hfiber g i ) ) : weq X ( stn ( stnsum f ) ) .
Proof. intros . assert ( w : weq X ( total2 ( fun i : stn n => hfiber g i ) ) ) . apply weqtococonusf . apply ( weqcomp w ( weqstnsum ( fun i : stn n => hfiber g i ) f ww ) ) .   Defined . 



(** *** Weak equivalence between the direct product of [ stn n ] and [ stn m ] and [ stn n * m ] *)

Theorem weqfromprodofstn ( n m : nat ) : weq ( dirprod ( stn n ) ( stn m ) ) ( stn ( n * m ) ) .
Proof .  intros . destruct ( boolchoice ( leb m 0 ) ) as [ i | is ] . set ( e := leh0implis0 _ i ) .  rewrite e .  rewrite ( multn0 n ) . split with ( @pr22 _ _ ) .   apply ( isweqtoempty2 _ ( weqstn0toempty ) ) .
assert ( i1 : forall i j : nat , lth i n -> lth j m ->  lth ( j + i * m ) ( n * m ) ).  intros i j li lj . apply ( lthlehtrans ( j + i * m ) ( ( S i ) * m ) ( n * m ) ( gthandplusr m j ( i * m ) lj ) ( lehandmultr ( S i ) n m ( gthimplgehsn _ _ li ) ) ) .     

set ( f := fun ij : dirprod ( stn n ) ( stn m ) => match ij with tpair i j => stnpair ( n * m ) ( j + i * m ) ( i1 i j ( pr22 i ) ( pr22 j ) ) end ) .  split with f . 

assert ( isinf : isincl f ) . apply isinclbetweensets . apply ( isofhleveldirprod 2 _ _ ( isasetstn n ) ( isasetstn m ) ) .  apply ( isasetstn ( n * m ) ) . intros ij ij' e .  destruct ij as [ i j ] . destruct ij' as [ i' j' ] .  destruct i as [ i li ] . destruct i' as [ i' li' ] .  destruct j as [ j lj ] . destruct j' as [ j' lj' ] . simpl in e . assert ( e' := maponpaths ( stntonat ( n * m ) ) e )  .   simpl in e' .
assert ( eei : paths i i' ) . apply ( pr21 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) .    
set ( eeis := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ i li ) ( stnpair _ i' li' ) eei ) .
assert ( eej : paths j j' ) . apply ( pr22 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) . 
set ( eejs := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ j lj ) ( stnpair _ j' lj' ) eej ) . apply ( pathsdirprod eeis eejs ) . 

intro xnm .  apply iscontraprop1 . apply ( isinf xnm ) . set ( e := pathsinv0 ( natdivremrule xnm m is ) ) .  set ( i := natdiv xnm m is ) .   set ( j := natrem xnm m is ) . destruct xnm as [ xnm lxnm ] .   set ( li := lthandmultrinv _ _ _ is ( lehlthtrans _ _ _ ( lehmultnatdiv xnm m is ) lxnm ) ) .  set ( lj := lthnatrem xnm m is ) .  split with ( dirprodpair ( stnpair n i li ) ( stnpair m j lj ) ) .  simpl . apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _ ) .  simpl . apply e . Defined . 


(** *** Weak equivalences between decidable subsets of [ stn n ] and [ stn x ] *)

Theorem weqfromdecsubsetofstn { n : nat } ( f : stn n -> bool ) : total2 ( fun x : nat => weq ( hfiber f true ) ( stn x ) ) .
Proof . intro . induction n as [ | n IHn ] . intros .    split with 0 .  assert ( g : ( hfiber f true ) -> ( stn 0 ) ) . intro hf . destruct hf as [ i e ] .  destruct ( weqstn0toempty i ) .  apply ( weqtoempty2 g weqstn0toempty ) . intro . set ( g := weqfromcoprodofstn 1 n ) .   change ( 1 + n ) with ( S n ) in g . 

set ( fl := fun i : stn 1 => f ( g ( ii1 i ) ) ) .   set ( fh := fun i : stn n => f ( g ( ii2 i ) ) ) . assert ( w : weq ( hfiber f true ) ( hfiber ( sumofmaps fl fh ) true ) ) .  set ( int := invweq ( weqhfibersgwtog g f true  ) ) .  assert ( h : forall x : _ , paths ( f ( g x ) ) ( sumofmaps fl fh x ) ) . intro . destruct x as [ x1 | xn ] . apply idpath . apply idpath .   apply ( weqcomp int ( weqhfibershomot _ _ h true ) ) .  set ( w' := weqcomp w ( invweq ( weqhfibersofsumofmaps fl fh true ) ) ) .  

set ( x0 := pr21 ( IHn fh ) ) . set ( w0 := pr22 ( IHn fh ) ) . simpl in w0 . destruct ( boolchoice ( fl ( lastelement 0 ) ) ) as [ i | ni ] .  

split with ( S x0 ) .  assert ( wi : weq ( hfiber fl true ) ( stn 1 ) ) . assert ( is : iscontr ( hfiber fl true ) ) . apply iscontraprop1 . apply ( isinclfromstn1 fl isasetbool true ) .  apply ( hfiberpair _ ( lastelement 0 ) i ) . apply ( weqcontrcontr is iscontrstn1 ) .  apply ( weqcomp ( weqcomp w' ( weqcoprodf wi w0 ) ) ( weqfromcoprodofstn 1 _ ) ) . 

split with x0 .  assert ( g' : neg ( hfiber fl true ) ) . intro hf . destruct hf as [ j e ] .  assert ( ee : paths j ( lastelement 0 ) ) . apply ( proofirrelevance _ ( isapropifcontr iscontrstn1 ) _ _ ) .  destruct ( nopathstruetofalse ( pathscomp0 ( pathscomp0 ( pathsinv0 e ) ( maponpaths fl ee ) ) ni ) ) .  apply ( weqcomp w' ( weqcomp ( invweq ( weqii2withneg _ g' ) ) w0 )  )  .  Defined . 

(** *** Weak equivalences between hfibers of functions from [ stn n ] over isolated points and [ stn x ] *)

Theorem weqfromhfiberfromstn { n : nat } { X : UU0 } ( x : X ) ( is : isisolated X x ) ( f : stn n -> X ) : total2 ( fun x0 : nat => weq ( hfiber f x ) ( stn x0 ) ) .
Proof . intros .  set ( t := weqfromdecsubsetofstn ( fun i : _ => eqbx X x is ( f i ) ) ) . split with ( pr21 t ) . apply ( weqcomp ( weqhfibertobhfiber f x is ) ( pr22 t ) ) .   Defined . 





(** *** Weak equivalence between [ stn n -> stn m ] and [ stn ( natpower m n ) ] ( uses functional extensionality ) *) 


Theorem weqfromfunstntostn ( n m : nat ) : weq ( stn n -> stn m ) ( stn ( natpower m n ) ) .
Proof. intro n . induction n as [ | n IHn ] . intro m .  apply weqcontrcontr . apply ( iscontrfunfromempty2 _ weqstn0toempty ) .  apply iscontrstn1 .
intro m . set ( w1 := weqfromcoprodofstn 1 n ) . assert ( w2 : weq ( stn ( S n ) -> stn m ) ( (coprod (stn 1) (stn n)) -> stn m ) ) .   apply ( weqbfun _ w1  ) .  set ( w3 := weqcomp w2 ( weqfunfromcoprodtoprod ( stn 1 ) ( stn n ) ( stn m ) ) ) .   set ( w4 := weqcomp w3 ( weqdirprodf ( weqfunfromcontr ( stn m ) iscontrstn1 ) ( IHn m ) ) ) .  apply ( weqcomp w4 ( weqfromprodofstn m ( natpower m n ) ) ) .  Defined . 





(** *** Weak equivalence from the space of functions of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnprod n f ) ] ( uses functional extensionality ) *)

Definition stnprod { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 1 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) * f ( lastelement n ) ) . Defined . 

Theorem weqstnprod { n : nat } ( P : stn n -> UU0 ) ( f : stn n -> nat ) ( ww : forall i : stn n , weq ( stn ( f i ) )  ( P i ) ) : weq ( forall x : stn n , P x  ) ( stn ( stnprod f ) ) .
Proof . intro n . induction n as [ | n IHn ] . intros . simpl . apply ( weqcontrcontr ) .  apply ( iscontrsecoverempty2 _ ( negstn0 ) ) .   apply iscontrstn1 . intros .  set ( w1 := weqdnicoprod n ( lastelement n ) ) . set ( w2 := weqonsecbase P w1 ) .   set ( w3 := weqsecovercoprodtoprod ( fun x : _ => P ( w1 x ) ) ) .  set ( w4 := weqcomp w2 w3 ) .  set ( w5 := IHn ( fun x : stn n => P ( w1 ( ii1 x ) ) ) ( fun x : stn n => f ( w1 ( ii1 x ) ) ) ( fun i : stn n => ww ( w1 ( ii1 i ) ) ) ) . set ( w6 := weqcomp w4 ( weqdirprodf w5 ( weqsecoverunit _ ) ) ) .  simpl in w6 .  set ( w7 := weqcomp w6 ( weqdirprodf ( idweq _ ) ( invweq ( ww ( lastelement n ) ) ) ) ) .  apply ( weqcomp w7 ( weqfromprodofstn _ _ ) ) .   Defined . 




(** *** Weak equivalence between [ weq ( stn n ) ( stn n ) ] and [ stn ( factorial n ) ] ( uses functional extensionality ) *)

Theorem  weqweqstnsn ( n : nat ) : weq ( weq ( stn ( S n ) ) ( stn ( S n ) ) ) ( dirprod ( stn ( S n ) ) ( weq ( stn n ) ( stn n ) ) ) .
Proof . intro . set ( nn := lastelement n ) . set ( is := isdeceqstn _ nn ) . set ( w1 := weqcutonweq ( stn ( S n ) ) nn is ) . set ( w2 := weqisolatedstntostn ( S n ) ) .  set ( w3 := invweq ( weqdnicompl n nn ) ) .  apply ( weqcomp w1 ( weqdirprodf w2 ( weqcomp ( weqbweq _ ( invweq w3 )) ( weqfweq _ w3 ) ) ) ) .  Defined .   


Theorem weqfromweqstntostn ( n : nat ) : weq ( weq ( stn n ) ( stn n ) ) ( stn ( factorial n ) ) . 
Proof . intro . induction n as [ | n IHn ] . simpl . apply ( weqcontrcontr ) . apply ( iscontraprop1 ) .    apply ( isapropweqtoempty2 _ ( negstn0 ) ) .  apply idweq . apply iscontrstn1 . change ( factorial ( S n ) ) with ( ( S n ) * ( factorial n ) ) .   set ( w1 := weqweqstnsn n ) . apply ( weqcomp w1 ( weqcomp ( weqdirprodf ( idweq _ ) IHn ) ( weqfromprodofstn _ _ ) ) ) .  Defined . 


(* End of " weak equivalences between standard finite sets and constructions on these sets " . *)







(** ** Standard finite sets satisfy weak axiom of choice *)

Theorem ischoicebasestn ( n : nat ) : ischoicebase ( stn n ) .
Proof . intro . induction n as [ | n IHn ] .  apply ( ischoicebaseempty2 negstn0 ) .  apply ( ischoicebaseweqf ( weqdnicoprod n ( lastelement n ) ) ( ischoicebasecoprod IHn ischoicebaseunit ) ) .  Defined . 







(** ** Weak equivalence class of [ stn n ] determines [ n ] . *)


Lemma negweqstnsn0 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr21 X lp). Defined.

Lemma negweqstn0sn (n:nat): neg (weq (stn O) (stn (S n))).
Proof.  unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr21 ( invweq X ) lp). Defined.

Lemma weqcutforstn ( n n' : nat ) ( w : weq (stn (S n)) (stn (S n')) ) : weq (stn n) (stn n').
Proof. intros. set ( nn := lastelement n  ) . set ( w1 := weqoncompl w nn ) .  set ( w2 := weqdnicompl n nn ) . set ( w3 := weqdnicompl n' ( w nn ) ) .   apply ( weqcomp w2 ( weqcomp w1 ( invweq w3 ) ) ) . Defined .   


Theorem weqtoeqstn ( n n' : nat ) ( w : weq (stn n) (stn n') ) : paths n n'.
Proof. intro. induction n as [ | n IHn ] . intro. destruct n' as [ | n' ] .  intros. apply idpath. intro X. apply (fromempty (negweqstn0sn  n' X)).  
 intro n'. destruct n' as [ | n' ] . intro X. set (int:= isdeceqnat (S n) 0 ).  destruct int as [ i | e ] .  assumption. apply (fromempty ( negweqstnsn0 n X)).  intro X. 
set (e:= IHn n' ( weqcutforstn _ _ X)). apply (maponpaths S e). Defined. 

Corollary stnsdnegweqtoeq ( n n' : nat ) ( dw : dneg (weq (stn n) (stn n')) ) : paths n n'.
Proof. intros n n' X. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf (@weqtoeqstn n n') X)). Defined. 







(* End of the file stnfsets.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

