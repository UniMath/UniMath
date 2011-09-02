(** * Standard algebraic structures. Vladimir Voevodsky. Aug. - Sep. 2011 . 

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hSet .


(** To upstream files *)


Lemma isinclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : isincl ( funcomp ( pr21 f ) ( pr21 g ) ) .
Proof . intros . apply ( isofhlevelfgf 1 f g ( pr22 f ) ( pr22 g ) ) . Defined . (* + *)

Definition inclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : incl X Z := inclpair ( funcomp ( pr21 f ) ( pr21 g ) ) ( isinclcomp f g ) . (* + *)





(** ** Sets with one and two binary operations *)

(** *** Binary operations *)

(** **** General definitions *)

Definition binop ( X : UU0 ) := X -> X -> X .

Definition islcancellable { X : UU0 } ( opp : binop X ) ( x : X ) := isincl ( fun x0 : X => opp x x0 ) .

Definition isrcancellable { X : UU0 } ( opp : binop X ) ( x : X ) := isincl ( fun x0 : X => opp x0 x ) .

Definition iscancellable { X : UU0 } ( opp : binop X ) ( x : X )  := dirprod ( islcancellable opp x ) ( isrcancellable opp x ) . 

Definition islinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := isweq ( fun x0 : X => opp x x0 ) .

Definition isrinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := isweq ( fun x0 : X => opp x0 x ) .

Definition isinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := dirprod ( islinvertible opp x ) ( isrinvertible opp x ) . 



(** **** Standard conditions on one binary operation on a set *)

(** *)

Definition isassoc { X : hSet} ( opp : binop X ) := forall x x' x'' , paths ( opp ( opp x x' ) x'' ) ( opp x ( opp x' x'' ) ) .

Lemma isapropisassoc { X : hSet } ( opp : binop X ) : isaprop ( isassoc opp ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .

(** *)

Definition islunit { X : hSet} ( opp : binop X ) ( un0 : X ) := forall x : X , paths ( opp un0 x ) x .

Lemma isapropislunit { X : hSet} ( opp : binop X ) ( un0 : X ) : isaprop ( islunit opp un0 ) . 
Proof . intros . apply impred . intro x . simpl . apply ( setproperty X ) .  Defined .  

Definition isrunit { X : hSet} ( opp : binop X ) ( un0 : X ) := forall x : X , paths ( opp x un0 ) x  .

Lemma isapropisrunit { X : hSet} ( opp : binop X ) ( un0 : X ) : isaprop ( isrunit opp un0 ) .
Proof . intros . apply impred . intro x . simpl . apply ( setproperty X ) .  Defined .  

Definition isunit { X : hSet} ( opp : binop X ) ( un0 : X ) := dirprod ( islunit opp un0 ) ( isrunit opp un0 ) .

Definition isunital { X : hSet} ( opp : binop X ) := total2 ( fun un0 : X => isunit opp un0 ) .
Definition isunitalpair { X : hSet } { opp : binop X } ( un0 : X ) ( is : isunit opp un0 ) : isunital opp := tpair _ un0 is .  

Lemma isapropisunital { X : hSet} ( opp : binop X )  : isaprop ( isunital opp ) .
Proof . intros .  apply ( @isapropsubtype X ( fun un0 : _ => hconj ( hProppair _ ( isapropislunit opp un0 ) ) ( hProppair _ ( isapropisrunit opp un0 ) ) ) )  .  intros u1 u2 .  intros ua1 ua2 .  apply ( pathscomp0 ( pathsinv0 ( pr22 ua2 u1 ) ) ( pr21 ua1 u2 ) ) .  Defined . 


(** *)

Definition ismonoidop { X : hSet } ( opp : binop X ) := dirprod ( isassoc opp ) ( isunital opp ) .
Definition assocax_is { X : hSet } { opp : binop X } : ismonoidop opp -> isassoc opp := @pr21 _ _ .  
Definition unel_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) : X := pr21 ( pr22 is ) .
Definition lunax_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) := pr21 ( pr22 ( pr22 is ) ) . 
Definition runax_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) := pr22 ( pr22 ( pr22 is ) ) . 


Lemma isapropismonoidop { X : hSet } ( opp : binop X ) : isaprop ( ismonoidop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply ( isapropisassoc ) .  apply ( isapropisunital ) .  Defined .  



(** *)

Definition islinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := forall x : X , paths ( opp ( inv0 x ) x ) un0 .

Lemma isapropislinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( islinv opp un0 inv0 ) .
Proof . intros . apply impred . intro x .  apply ( setproperty X (opp (inv0 x) x) un0 ) . Defined .

Definition isrinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := forall x : X , paths ( opp x ( inv0 x ) ) un0 .

Lemma isapropisrinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( isrinv opp un0 inv0 ) .
Proof . intros . apply impred . intro x .  apply ( setproperty X ) . Defined .

Definition isinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := dirprod ( islinv opp un0 inv0 ) ( isrinv opp un0 inv0 ) . 

Lemma isapropisinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( isinv opp un0 inv0 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropislinv .  apply isapropisrinv . Defined .  

Definition invstruct { X : hSet } ( opp : binop X ) ( is : ismonoidop opp  ) := total2 ( fun inv0 : X -> X =>  isinv opp ( unel_is is ) inv0 ) .

Definition isgroupop { X : hSet } ( opp : binop X ) := total2 ( fun is : ismonoidop opp => invstruct opp is ) .
Definition isgroupoppair { X : hSet } { opp : binop X } ( is1 : ismonoidop opp ) ( is2 : invstruct opp is1 ) : isgroupop opp := tpair ( fun is : ismonoidop opp => invstruct opp is ) is1 is2 . 
Definition pr21isgroupop ( X : hSet ) ( opp : binop X ) : isgroupop opp -> ismonoidop opp := @pr21 _ _ .
Coercion pr21isgroupop : isgroupop >-> ismonoidop . 

Definition grinv_is { X : hSet } { opp : binop X } ( is : isgroupop opp ) : X -> X := pr21 ( pr22 is ) . 

Definition grlinvax_is { X : hSet } { opp : binop X } ( is : isgroupop opp ) := pr21 ( pr22 ( pr22 is ) ) . 

Definition grrinvax_is { X : hSet } { opp : binop X } ( is : isgroupop opp ) := pr22 ( pr22 ( pr22 is ) ) . 


Lemma isweqrmultingr_is { X : hSet } { opp : binop X } ( is : isgroupop opp ) ( x0 : X ) : isrinvertible opp x0 .
Proof . intros .  destruct is as [ is istr ] . set ( f := fun x : X => opp x x0 ) . set ( g := fun x : X , opp x ( ( pr21 istr ) x0 ) ) .  destruct is as [ assoc isun0 ] . destruct istr as [ inv0 axs ] .   destruct isun0 as [ un0 unaxs ] .  simpl in * |-  . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x . unfold f . unfold g . destruct ( pathsinv0 ( assoc x x0 ( inv0 x0 ) ) ) .  assert ( e := pr22 axs x0 ) .   simpl in e . rewrite e . apply ( pr22 unaxs x ) .  
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x .  unfold f . unfold g . destruct ( pathsinv0 ( assoc x ( inv0 x0 ) x0 ) ) . assert ( e := pr21 axs x0 ) . simpl in e . rewrite e . apply ( pr22 unaxs x ) .  
apply ( gradth _ _ egf efg ) . Defined .  

Lemma isweqlmultingr_is { X : hSet } { opp : binop X } ( is : isgroupop opp )  ( x0 : X ) : islinvertible opp x0 .
Proof . intros .   destruct is as [ is istr ] .  set ( f := fun x : X => opp x0 x ) . set ( g := fun x : X , opp ( ( pr21 istr ) x0 ) x ) .  destruct is as [ assoc isun0 ] . destruct istr as [ inv0 axs ] .  destruct isun0 as [ un0 unaxs ] .  simpl in * |-  . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x . unfold f . unfold g . destruct ( assoc ( inv0 x0 ) x0 x  ) . assert ( e := pr21 axs x0 ) . simpl in e . rewrite e . apply ( pr21 unaxs x ) .  
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x . unfold f . unfold g . destruct ( assoc x0 ( inv0 x0 ) x  ) . assert ( e := pr22 axs x0 ) . simpl in e . rewrite e . apply ( pr21 unaxs x ) .  
apply ( gradth _ _ egf efg ) . Defined .  


Lemma isapropinvstruct { X : hSet } { opp : binop X } ( is : ismonoidop opp ) : isaprop ( invstruct opp is ) . 
Proof . intros . apply isofhlevelsn . intro is0 . set ( un0 := pr21 ( pr22 is ) ) . assert ( int : forall i : X -> X , isaprop ( dirprod ( forall x : X , paths ( opp ( i x ) x ) un0 ) ( forall x : X , paths ( opp x ( i x ) ) un0 ) ) ) . intro i . apply ( isofhleveldirprod 1 ) .  apply impred . intro x .  simpl . apply ( setproperty X  ) . apply impred . intro x .   simpl .  apply ( setproperty X ) . apply ( isapropsubtype ( fun i : _ => hProppair _ ( int i ) ) ) .  intros inv1 inv2 .  simpl . intro ax1 .  intro ax2 .  apply funextfun . intro x0 . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is ( tpair _ is is0 ) x0 ) ) ) .    simpl . rewrite ( pr21 ax1 x0 ) .   rewrite ( pr21 ax2 x0 ) .  apply idpath .  Defined . 

Lemma isapropisgroupop { X : hSet } ( opp : binop X ) : isaprop ( isgroupop opp ) .
Proof . intros . apply ( isofhleveltotal2 1 ) . apply isapropismonoidop . apply isapropinvstruct . Defined .  

(* (** Unitary monoid where all elements are invertible is a group *)

Definition allinvvertibleinv { X : hSet } { opp : binop X } ( is : ismonoidop opp ) ( allinv : forall x : X , islinvertible opp x ) : X -> X := fun x : X => invmap ( weqpair _ ( allinv x ) ) ( unel_is is ) .   

*)


(** The following lemma is an analog of [ Bourbaki , Alg. 1 , ex. 2 , p. 132 ] *)

Lemma isgroupopif { X : hSet } { opp : binop X } ( is0 : ismonoidop opp ) ( is : forall x : X, hexists ( fun x0 : X => eqset ( opp x x0 ) ( unel_is is0 ) ) ) : isgroupop opp . 
Proof . intros . split with is0 .  destruct is0 as [ assoc isun0 ] . destruct isun0 as [ un0 unaxs0 ] . simpl in is .  simpl in unaxs0 . simpl in un0 . simpl in assoc . simpl in unaxs0 .  

assert ( l1 : forall x' : X , isincl ( fun x0 : X => opp x0 x' ) ) . intro x' . apply ( @hinhuniv ( total2 ( fun x0 : X => paths ( opp x' x0 ) un0 ) ) ( hProppair _ ( isapropisincl ( fun x0 : X => opp x0 x' ) ) ) ) .  intro int1 . simpl . apply isinclbetweensets .  apply ( pr22 X ) .  apply ( pr22 X ) .   intros a b .  intro e .  rewrite ( pathsinv0 ( pr22 unaxs0 a ) ) . rewrite ( pathsinv0 ( pr22 unaxs0 b ) ) .  destruct int1 as [ invx' eq ] .  rewrite ( pathsinv0 eq ) . destruct ( assoc a x' invx' ) .  destruct ( assoc b x' invx' ) .  rewrite e . apply idpath .  apply ( is x' ) .  

assert ( is' :  forall x : X, hexists ( fun x0 : X => eqset ( opp x0 x ) un0 ) ) . intro x . apply ( fun f : _ => @hinhuniv _ ( hexists (fun x0 : X => eqset (opp x0 x) un0) ) f ( is x ) ) .  intro s1 .  destruct s1 as [ x' eq ] .  apply hinhpr . split with x' . simpl . apply ( invmaponpathsincl _ ( l1 x' ) ) .   rewrite ( assoc x' x x' ) . rewrite eq .  rewrite ( pr21 unaxs0 x' ) . unfold unel_is.   simpl . rewrite ( pr22 unaxs0 x' ) .  apply idpath . 

assert ( l1' :  forall x' : X , isincl ( fun x0 : X => opp x' x0 ) ) . intro x' . apply ( @hinhuniv ( total2 ( fun x0 : X => paths ( opp x0 x' ) un0 ) ) ( hProppair _ ( isapropisincl ( fun x0 : X => opp x' x0 ) ) ) ) .  intro int1 . simpl . apply isinclbetweensets .  apply ( pr22 X ) .  apply ( pr22 X ) .   intros a b .  intro e .  rewrite ( pathsinv0 ( pr21 unaxs0 a ) ) . rewrite ( pathsinv0 ( pr21 unaxs0 b ) ) .  destruct int1 as [ invx' eq ] .  rewrite ( pathsinv0 eq ) . destruct ( pathsinv0 ( assoc invx' x' a )  ) .  destruct ( pathsinv0 ( assoc invx' x' b ) ) .  rewrite e . apply idpath .  apply ( is' x' ) .  

assert ( int : forall x : X , isaprop ( total2 ( fun x0 : X => eqset ( opp x0 x ) un0 ) ) ) . intro x .   apply isapropsubtype .  intros x1 x2 .  intros eq1 eq2 .  apply ( invmaponpathsincl _ ( l1 x ) ) . rewrite eq1 .   rewrite eq2 .  apply idpath . 

simpl . set ( linv0 := fun x : X => hinhunivcor1 ( hProppair _ ( int x ) ) ( is' x ) ) .  simpl in linv0 .  set ( inv0 := fun x : X => pr21 ( linv0 x ) ) .  split with inv0 . simpl . split with ( fun x : _ => pr22 ( linv0 x ) ) .  intro x .  apply ( invmaponpathsincl _ ( l1 x ) ) . rewrite ( assoc x ( inv0 x ) x ) . change ( inv0 x ) with ( pr21 ( linv0 x ) ) . rewrite ( pr22 ( linv0 x ) ) . unfold unel_is . simpl . rewrite ( pr21 unaxs0 x ) . rewrite ( pr22 unaxs0 x ) . apply idpath .  Defined . 



(** *)

Definition iscomm { X : hSet} ( opp : binop X ) := forall x x' : X , paths ( opp x x' ) ( opp x' x ) . 

Lemma isapropiscomm { X : hSet } ( opp : binop X ) : isaprop ( iscomm opp ) .
Proof . intros . apply impred . intros x . apply impred . intro x' . simpl . apply ( setproperty X ) . Defined . 

Definition isabmonoidop { X : hSet } ( opp : binop X ) := dirprod ( ismonoidop opp ) ( iscomm opp ) . 
Definition pr21isabmonoidop ( X : hSet ) ( opp : binop X ) : isabmonoidop opp -> ismonoidop opp := @pr21 _ _ .
Coercion pr21isabmonoidop : isabmonoidop >-> ismonoidop .

Definition commax_is { X : hSet} { opp : binop X } ( is : isabmonoidop opp ) : iscomm opp := pr22 is . 

Lemma isapropisabmonoidop { X : hSet } ( opp : binop X ) : isaprop ( isabmonoidop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropismonoidop . apply isapropiscomm . Defined . 

Lemma abmonoidoprer { X : hSet } { opp : binop X } ( is : isabmonoidop opp ) ( a b c d : X ) : paths ( opp ( opp a b ) ( opp c d ) ) ( opp ( opp a c ) ( opp b d ) ) .
Proof . intros . destruct is as [ is comm ] . destruct is as [ assoc unital0 ] .  simpl in * .  destruct ( assoc ( opp a b ) c d ) .  destruct ( assoc ( opp a c ) b d ) . destruct ( pathsinv0 ( assoc a b c ) ) . destruct ( pathsinv0 ( assoc a c b ) ) .   destruct ( comm b c ) . apply idpath .  Defined . 




(** *)


Lemma weqlcancellablercancellable { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( x : X ) : weq ( islcancellable opp x ) ( isrcancellable opp x ) .
Proof . intros . 

assert ( f : ( islcancellable opp x ) -> ( isrcancellable opp x ) ) . unfold islcancellable . unfold isrcancellable .  intro isl . apply ( fun h : _ => isinclhomot _ _ h isl ) .  intro x0 . apply is .  
assert ( g : ( isrcancellable opp x ) -> ( islcancellable opp x ) ) . unfold islcancellable . unfold isrcancellable .  intro isr . apply ( fun h : _ => isinclhomot _ _ h isr ) .  intro x0 . apply is . 

split with f . apply ( isweqimplimpl f g ( isapropisincl ( fun x0 : X => opp x x0 ) )  ( isapropisincl ( fun x0 : X => opp x0 x ) ) ) .  Defined .  



Lemma weqlinvertiblerinvertible { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( x : X ) : weq ( islinvertible opp x ) ( isrinvertible opp x ) .
Proof . intros . 

assert ( f : ( islinvertible opp x ) -> ( isrinvertible opp x ) ) . unfold islinvertible . unfold isrinvertible .  intro isl . apply ( fun h : _ => isweqhomot _ _ h isl ) .  apply is .  
assert ( g : ( isrinvertible opp x ) -> ( islinvertible opp x ) ) . unfold islinvertible . unfold isrinvertible .  intro isr . apply ( fun h : _ => isweqhomot _ _ h isr ) .  intro x0 . apply is . 

split with f . apply ( isweqimplimpl f g ( isapropisweq ( fun x0 : X => opp x x0 ) )  ( isapropisweq ( fun x0 : X => opp x0 x ) ) ) .  Defined .  


Lemma weqlunitrunit { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( un0 : X ) : weq ( islunit opp un0 ) ( isrunit opp un0 ) .
Proof . intros . 

assert ( f : ( islunit opp un0 ) -> ( isrunit opp un0 ) ) . unfold islunit . unfold isrunit .  intro isl .  intro x .  destruct ( is un0 x ) .  apply ( isl x ) .  
assert ( g : ( isrunit opp un0 ) -> ( islunit opp un0 ) ) . unfold islunit . unfold isrunit .  intro isr . intro x .  destruct ( is x un0 ) .  apply ( isr x ) .  

split with f . apply ( isweqimplimpl f g ( isapropislunit opp un0 )  ( isapropisrunit opp un0 ) ) .  Defined .  


Lemma weqlinvrinv { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( un0 : X ) ( inv0 : X -> X ) : weq ( islinv opp un0 inv0 ) ( isrinv opp un0 inv0 ) .
Proof . intros . 

assert ( f : ( islinv opp un0 inv0 ) -> ( isrinv opp un0 inv0 ) ) . unfold islinv . unfold isrinv .  intro isl .  intro x .  destruct ( is ( inv0 x ) x ) .  apply ( isl x ) .  
assert ( g : ( isrinv opp un0 inv0 ) -> ( islinv opp un0 inv0 ) ) . unfold islinv . unfold isrinv .  intro isr . intro x .  destruct ( is x ( inv0 x ) ) .  apply ( isr x ) .  

split with f . apply ( isweqimplimpl f g ( isapropislinv opp un0 inv0 )  ( isapropisrinv opp un0 inv0 ) ) .  Defined .  


Opaque abmonoidoprer .


(** *)

Definition isabgroupop { X : hSet } ( opp : binop X ) := dirprod ( isgroupop opp ) ( iscomm opp ) .
Definition pr21isabgroupop ( X : hSet ) ( opp : binop X ) : isabgroupop opp -> isgroupop opp := @pr21 _ _ .
Coercion pr21isabgroupop : isabgroupop >-> isgroupop .

Definition isabgroupoptoisabmonoidop ( X : hSet ) ( opp : binop X ) : isabgroupop opp -> isabmonoidop opp := fun is : _ => dirprodpair ( pr21 ( pr21 is ) ) ( pr22 is ) .
Coercion isabgroupoptoisabmonoidop : isabgroupop >-> isabmonoidop .

Lemma isapropisabgroupop { X : hSet } ( opp : binop X ) : isaprop ( isabgroupop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropisgroupop . apply isapropiscomm . Defined .  








(** **** Standard conditions on a pair of binary operations on a set *)

(** *)

Definition isldistr { X : hSet} ( opp1 opp2 : binop X ) := forall x x' x'' : X , paths ( opp2 x'' ( opp1 x x' ) ) ( opp1 ( opp2 x'' x ) ( opp2 x'' x' ) ) .

Lemma isapropisldistr { X : hSet} ( opp1 opp2 : binop X ) : isaprop ( isldistr opp1 opp2 ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .   

Definition isrdistr { X : hSet} ( opp1 opp2 : binop X ) := forall x x' x'' : X , paths ( opp2 ( opp1 x x' ) x'' ) ( opp1 ( opp2 x x'' ) ( opp2 x' x'' ) ) .

Lemma isapropisrdistr { X : hSet} ( opp1 opp2 : binop X ) : isaprop ( isrdistr opp1 opp2 ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .   

Definition isdistr { X : hSet } ( opp1 opp2 : binop X ) := dirprod ( isldistr opp1 opp2 ) ( isrdistr opp1 opp2 ) .

Lemma isapropisdistr { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( isdistr opp1 opp2  ) .
Proof . intros . apply ( isofhleveldirprod 1 _ _ ( isapropisldistr _ _ ) ( isapropisrdistr _ _ ) ) . Defined .  

(** *)

Lemma weqldistrrdistr { X : hSet} ( opp1 opp2 : binop X ) ( is : iscomm opp2 ) : weq ( isldistr opp1 opp2 ) ( isrdistr opp1 opp2 ) .
Proof .  intros . 

assert ( f : ( isldistr opp1 opp2 ) -> ( isrdistr opp1 opp2 ) ) . unfold isldistr . unfold isrdistr .  intro isl .  intros x x' x'' .  destruct ( is x'' ( opp1 x x' ) ) . destruct ( is x'' x ) . destruct ( is x'' x' ) .  apply ( isl x x' x'' ) .  
assert ( g : ( isrdistr opp1 opp2 ) -> ( isldistr opp1 opp2 ) ) . unfold isldistr . unfold isrdistr .  intro isr .  intros x x' x'' .  destruct ( is ( opp1 x x' ) x'' ) . destruct ( is x x'' ) . destruct ( is x' x'' ) .  apply ( isr x x' x'' ) .   

split with f . apply ( isweqimplimpl f g ( isapropisldistr opp1 opp2 )  ( isapropisrdistr opp1 opp2 ) ) .  Defined . 









(** *)


Definition isrigops { X : hSet } ( opp1 opp2 : binop X ) :=  dirprod ( total2 ( fun axs : dirprod ( isabmonoidop opp1 ) ( ismonoidop opp2 ) => ( dirprod ( paths ( opp2 ( unel_is ( pr21 axs ) ) ( unel_is ( pr22 axs ) ) ) ( unel_is ( pr21 axs ) ) ) ( paths ( opp2 ( unel_is ( pr22 axs ) ) ( unel_is ( pr21 axs ) ) ) ( unel_is ( pr21 axs ) ) ) ) ) ) ( isdistr opp1 opp2 ) .
    




Definition isrngops { X : hSet } ( opp1 opp2 : binop X ) := dirprod ( dirprod ( isabgroupop opp1 ) ( ismonoidop opp2 ) ) ( isdistr opp1 opp2 ) . 

Definition op1axs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isabgroupop opp1 := fun is : _ => pr21 ( pr21 is ) .
Definition op2axs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> ismonoidop opp2 := fun is : _ => pr22 ( pr21 is ) .
Definition distraxs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isdistr opp1 opp2 := fun is : _ =>  pr22 is .
Definition ldistrax_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isldistr opp1 opp2 := fun is : _ => pr21 ( pr22 is ) .
Definition rdistrax_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isrdistr opp1 opp2 := fun is : _ => pr22 ( pr22 is ) .

Lemma isapropisrngops { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( isrngops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply ( isofhleveldirprod 1 ) . apply isapropisabgroupop . apply isapropismonoidop. apply isapropisdistr . Defined . 

Lemma multx0_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : forall x : X , paths ( opp2 x ( unel_is ( pr21 is1 ) ) ) ( unel_is ( pr21 is1 ) )  .
Proof . intros .  destruct is12 as [ ldistr0 rdistr0 ] . destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ] . simpl in * . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 x un2 ) ) ) ) .  simpl .  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ] .  unfold unel_is .  simpl in * . rewrite ( lun1 ( opp2 x un2 ) ) . destruct ( ldistr0 un1 un2 x ) .    rewrite ( run2 x ) .  rewrite ( lun1 un2 ) .  rewrite ( run2 x ) . apply idpath .  Defined .

Opaque multx0_is_l .

Lemma mult0x_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : forall x : X , paths ( opp2 ( unel_is ( pr21 is1 ) ) x ) ( unel_is ( pr21 is1 ) ) .
Proof . intros .  destruct is12 as [ ldistr0 rdistr0 ] . destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ] . simpl in * . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 un2 x ) ) ) ) .  simpl .  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ] .  unfold unel_is .  simpl in * . rewrite ( lun1 ( opp2 un2 x ) ) . destruct ( rdistr0 un1 un2 x ) .  rewrite ( lun2 x ) .  rewrite ( lun1 un2 ) .  rewrite ( lun2 x ) . apply idpath .  Defined .

Opaque mult0x_is_l .

Definition minus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) := ( grinv_is is1 ) ( unel_is is2 ) . 

Lemma islinvmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp1 ( opp2 ( minus1_is_l is1 is2 ) x ) x ) ( unel_is ( pr21 is1 ) ) .
Proof . intros . set ( xinv := opp2 (minus1_is_l is1 is2) x ) . rewrite ( pathsinv0 ( lunax_is is2 x ) ) . unfold xinv .  rewrite ( pathsinv0 ( pr22 is12 _ _ x ) ) . unfold minus1_is_l . unfold grinv_is . rewrite ( grlinvax_is is1 _ ) .  apply mult0x_is_l .   apply is2 . apply is12 .  Defined . 

Opaque islinvmultwithminus1_is_l .

Lemma isrinvmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp1 x ( opp2 ( minus1_is_l is1 is2 ) x ) ) ( unel_is ( pr21 is1 ) ) .
Proof . intros . set ( xinv := opp2 (minus1_is_l is1 is2) x ) . rewrite ( pathsinv0 ( lunax_is is2 x ) ) . unfold xinv .  rewrite ( pathsinv0 ( pr22 is12 _ _ x ) ) . unfold minus1_is_l . unfold grinv_is . rewrite ( grrinvax_is is1 _ ) .  apply mult0x_is_l .   apply is2 . apply is12 .  Defined . 

Opaque isrinvmultwithminus1_is_l . 


Lemma isminusmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp2 ( minus1_is_l is1 is2 ) x ) ( grinv_is is1 x ) .
Proof . intros . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 x ) ) ) .    simpl . rewrite ( islinvmultwithminus1_is_l is1 is2 is12 x ) . unfold grinv_is . rewrite ( grlinvax_is is1 x ) .  apply idpath . Defined . 

Opaque isminusmultwithminus1_is_l . 

Lemma isrngopsif { X : hSet } { opp1 opp2 : binop X } ( is1 : isgroupop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : isrngops opp1 opp2 .
Proof . intros .  set ( assoc1 := pr21 ( pr21 is1 ) ) . split . split .  split with is1 . 
intros x y .    apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 ( minus1_is_l is1 is2 ) ( opp1 x y ) ) ) ) ) . simpl . rewrite ( isrinvmultwithminus1_is_l is1 is2 is12 ( opp1 x y ) ) . rewrite ( pr21 is12 x y _ ) .  destruct ( assoc1 ( opp1 y x ) (opp2 (minus1_is_l is1 is2) x) (opp2 (minus1_is_l is1 is2) y)) . rewrite ( assoc1 y x _ ) . destruct ( pathsinv0 ( isrinvmultwithminus1_is_l is1 is2 is12 x ) ) . unfold unel_is .  rewrite ( runax_is ( pr21 is1 ) y ) . rewrite ( isrinvmultwithminus1_is_l is1 is2 is12 y ) .  apply idpath . apply is2 . apply is12 .  Defined .

Definition rngmultx0_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := multx0_is_l ( op1axs_is is ) ( op2axs_is is ) ( distraxs_is is )  .

Definition rngmult0x_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := mult0x_is_l ( op1axs_is is ) ( op2axs_is is ) ( distraxs_is is )  .

Definition rngminus1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := minus1_is_l ( op1axs_is is ) ( op2axs_is is ) .

Definition rngmultwithminus1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := isminusmultwithminus1_is_l ( op1axs_is is ) ( op2axs_is is ) ( distraxs_is is ) .
 



(** *) 

Definition iscommrngops { X : hSet } ( opp1 opp2 : binop X )  :=  dirprod ( isrngops opp1 opp2 ) ( iscomm opp2 ) . 
Definition pr21iscommrngops ( X : hSet ) ( opp1 opp2 : binop X ) : iscommrngops opp1 opp2 -> isrngops opp1 opp2 := @pr21 _ _ .
Coercion pr21iscommrngops : iscommrngops >-> isrngops .  

Definition iscommop2_is { X : hSet } { opp1 opp2 : binop X } ( is : iscommrngops opp1 opp2 ) : iscomm opp2 := pr22 is . 

Lemma isapropiscommrng  { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( iscommrngops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropisrngops . apply isapropiscomm . Defined . 







(** *** Sets with one binary operation *)

(** **** General definitions *)


Definition setwithbinop := total2 ( fun X : hSet => binop X ) . 
Definition setwithbinoppair ( X : hSet ) ( opp : binop X ) : setwithbinop := tpair ( fun X : hSet => binop X ) X opp .
Definition pr21setwithbinop : setwithbinop -> hSet := @pr21 _ ( fun X : hSet => binop X ) .
Coercion pr21setwithbinop : setwithbinop >-> hSet .


Definition op { X : setwithbinop } : binop X := pr22 X . 

Notation "x + y" := ( op x y ) : addoperation_scope .
Notation "x * y" := ( op x y ) : multoperation_scope .  



(** **** Functions compatible with a binary operation ( homomorphisms ) and their properties *)

Definition isbinopfun { X Y : setwithbinop } ( f : X -> Y ) := forall x x' : X , paths ( f ( op x x' ) ) ( op ( f x ) ( f x' ) ) . 

Lemma isapropisbinopfun { X Y : setwithbinop } ( f : X -> Y ) : isaprop ( isbinopfun f ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . Defined .

Definition binopfun ( X Y : setwithbinop ) : UU0 := total2 ( fun f : X -> Y => isbinopfun f ) .
Definition binopfunpair { X Y : setwithbinop } ( f : X -> Y ) ( is : isbinopfun f ) : binopfun X Y := tpair _ f is . 
Definition pr21binopfun ( X Y : setwithbinop ) : binopfun X Y -> ( X -> Y ) := @pr21 _ _ . 
Coercion pr21binopfun : binopfun >-> Funclass . 

Lemma isasetbinopfun  ( X Y : setwithbinop ) : isaset ( binopfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr21binopfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr21 .  intro .  apply isapropisbinopfun . Defined .  

Lemma isbinopfuncomp { X Y Z : setwithbinop } ( f : binopfun X Y ) ( g : binopfun Y Z ) : isbinopfun ( funcomp ( pr21 f ) ( pr21 g ) ) .
Proof . intros . set ( axf := pr22 f ) . set ( axg := pr22 g ) .  intros a b . unfold funcomp .  rewrite ( axf a b ) . rewrite ( axg ( pr21 f a ) ( pr21 f b ) ) .  apply idpath . Defined .  

Opaque isbinopfuncomp . 

Definition binopfuncomp { X Y Z : setwithbinop } ( f : binopfun X Y ) ( g : binopfun Y Z ) : binopfun X Z := binopfunpair ( funcomp ( pr21 f ) ( pr21 g ) ) ( isbinopfuncomp f g ) . 


Definition binopmono ( X Y : setwithbinop ) : UU0 := total2 ( fun f : incl X Y => isbinopfun ( pr21 f ) ) .
Definition binopmonopair { X Y : setwithbinop } ( f : incl X Y ) ( is : isbinopfun f ) : binopmono X Y := tpair _  f is .
Definition pr21binopmono ( X Y : setwithbinop ) : binopmono X Y -> incl X Y := @pr21 _ _ .
Coercion pr21binopmono : binopmono >-> incl .

Definition binopincltobinopfun ( X Y : setwithbinop ) : binopmono X Y -> binopfun X Y := fun f => binopfunpair ( pr21 ( pr21 f ) ) ( pr22 f ) .
Coercion binopincltobinopfun : binopmono >-> binopfun . 


Definition binopmonocomp { X Y Z : setwithbinop } ( f : binopmono X Y ) ( g : binopmono Y Z ) : binopmono X Z := binopmonopair ( inclcomp ( pr21 f ) ( pr21 g ) ) ( isbinopfuncomp f g ) . 

Definition binopiso ( X Y : setwithbinop ) : UU0 := total2 ( fun f : weq X Y => isbinopfun f ) .   
Definition binopisopair { X Y : setwithbinop } ( f : weq X Y ) ( is : isbinopfun f ) : binopiso X Y := tpair _  f is .
Definition pr21binopiso ( X Y : setwithbinop ) : binopiso X Y -> weq X Y := @pr21 _ _ .
Coercion pr21binopiso : binopiso >-> weq .

Definition binopisotobinopmono ( X Y : setwithbinop ) : binopiso X Y -> binopmono X Y := fun f => binopmonopair ( pr21 f ) ( pr22 f ) .
Coercion binopisotobinopmono : binopiso >-> binopmono . 

Definition binopisocomp { X Y Z : setwithbinop } ( f : binopiso X Y ) ( g : binopiso Y Z ) : binopiso X Z := binopisopair ( weqcomp ( pr21 f ) ( pr21 g ) ) ( isbinopfuncomp f g ) .

Lemma isbinopfuninvmap { X Y : setwithbinop } ( f : binopiso X Y ) : isbinopfun ( invmap ( pr21 f ) ) . 
Proof . intros . set ( axf := pr22 f ) . intros a b .  apply ( invmaponpathsweq ( pr21 f ) ) .  rewrite ( homotweqinvweq ( pr21 f ) ( op a b ) ) . rewrite ( axf (invmap (pr21 f) a) (invmap (pr21 f) b) ) .  rewrite ( homotweqinvweq ( pr21 f ) a ) .   rewrite ( homotweqinvweq ( pr21 f ) b ) .   apply idpath . Defined .

Opaque isbinopfuninvmap .  

Definition invbinopiso { X Y : setwithbinop } ( f : binopiso X Y ) : binopiso Y X := binopisopair ( invweq ( pr21 f ) ) ( isbinopfuninvmap f ) .



(** **** Transport of properties of a binary operation  *)


Lemma isincltwooutof3a { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isg : isincl g ) ( isgf : isincl ( funcomp f g ) ) : isincl f .
Proof . intros . apply ( isofhlevelff 1 f g isgf ) .  apply ( isofhlevelfsnincl 1 g isg ) . Defined .


Lemma islcancellablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : islcancellable ( @op Y ) ( f x ) ) : islcancellable ( @op X ) x .
Proof . intros .  unfold islcancellable . apply ( isincltwooutof3a (fun x0 : X => op x x0) f ( pr22 ( pr21 f ) ) ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op ( f x ) y0 ) ) (funcomp (fun x0 : X => op x x0) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr22 f ) x x0 ) ) . 

apply ( isinclhomot _ _ h ) . apply ( isinclcomp f ( inclpair _ is ) ) .  Defined .


Lemma isrcancellablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : isrcancellable ( @op Y ) ( f x ) ) : isrcancellable ( @op X ) x .
Proof . intros .  unfold islcancellable . apply ( isincltwooutof3a (fun x0 : X => op x0 x) f ( pr22 ( pr21 f ) ) ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op y0 ( f x ) ) ) (funcomp (fun x0 : X => op x0 x ) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr22 f ) x0 x ) ) . 

apply ( isinclhomot _ _ h ) . apply ( isinclcomp f ( inclpair _ is ) ) .  Defined .


Lemma iscancellablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : iscancellable ( @op Y ) ( f x ) ) : iscancellable ( @op X ) x . 
Proof . intros . apply ( dirprodpair ( islcancellablemonob f x ( pr21 is ) ) ( isrcancellablemonob f x ( pr22 is ) ) ) . Defined .

Notation islcancellableisob := islcancellablemonob . 
Notation isrcancellableisob := isrcancellablemonob . 
Notation iscancellableisob := iscancellablemonob .


Lemma islinvertibleisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : islinvertible ( @op Y ) ( f x ) ) : islinvertible ( @op X ) x .
Proof . intros .  unfold islinvertible . apply ( twooutof3a (fun x0 : X => op x x0) f ) .     

assert ( h : homot ( funcomp f ( fun y0 : Y => op ( f x ) y0 ) ) (funcomp (fun x0 : X => op x x0) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr22 f ) x x0 ) ) . 

apply ( isweqhomot _ _ h ) . apply ( pr22 ( weqcomp f ( weqpair _ is ) ) ) . apply ( pr22 ( pr21 f ) ) . Defined .  

Lemma isrinvertibleisob { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isrinvertible ( @op Y ) ( f x ) ) : isrinvertible ( @op X ) x .
Proof . intros .  unfold islinvertible . apply ( twooutof3a (fun x0 : X => op x0 x) f ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op y0 ( f x ) ) ) (funcomp (fun x0 : X => op x0 x ) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr22 f ) x0 x ) ) . 

apply ( isweqhomot _ _ h ) . apply ( pr22 ( weqcomp f ( weqpair _ is ) ) ) . apply ( pr22 ( pr21 f ) ) . Defined .


Lemma isinvertiblemonob { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isinvertible ( @op Y ) ( f x ) ) : isinvertible ( @op X ) x . 
Proof . intros . apply ( dirprodpair ( islinvertibleisob f x ( pr21 is ) ) ( isrinvertibleisob f x ( pr22 is ) ) ) . Defined .


Definition islinvertibleisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : islinvertible ( @op X ) x ) : islinvertible ( @op Y ) ( f x ) .
Proof . intros . unfold islinvertible . apply ( twooutof3b f ) .  apply ( pr22 ( pr21 f ) ) .    

assert ( h : homot ( funcomp ( fun x0 : X => op x x0 ) f ) (fun x0 : X => op (f x) (f x0))  ) .  intro x0 .  unfold funcomp .   apply ( pr22 f x x0 ) .

apply ( isweqhomot _ _ h ) . apply ( pr22 ( weqcomp ( weqpair _ is ) f ) ) . Defined .  

Definition isrinvertibleisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isrinvertible ( @op X ) x ) : isrinvertible ( @op Y ) ( f x ) .
Proof . intros . unfold isrinvertible . apply ( twooutof3b f ) .  apply ( pr22 ( pr21 f ) ) .    

assert ( h : homot ( funcomp ( fun x0 : X => op x0 x ) f ) (fun x0 : X => op (f x0) (f x) )  ) .  intro x0 .  unfold funcomp .   apply ( pr22 f x0 x ) .

apply ( isweqhomot _ _ h ) . apply ( pr22 ( weqcomp ( weqpair _ is ) f ) ) . Defined . 

Lemma isinvertiblemonof { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isinvertible ( @op X ) x ) : isinvertible ( @op Y ) ( f x ) . 
Proof . intros . apply ( dirprodpair ( islinvertibleisof f x ( pr21 is ) ) ( isrinvertibleisof f x ( pr22 is ) ) ) . Defined .


Lemma isassocmonob { X Y : setwithbinop } ( f : binopmono X Y ) ( is : isassoc ( @op Y ) ) : isassoc ( @op X ) .
Proof . intros . set ( axf := pr22 f ) .  simpl in axf .  intros a b c . apply ( invmaponpathsincl _ ( pr22 ( pr21 f ) ) ) . rewrite ( axf ( op a b ) c ) .  rewrite ( axf a b ) . rewrite ( axf a ( op b c ) ) . rewrite ( axf b c ) . apply is . Defined .   

Opaque isassocmonob .

Lemma iscommmonob { X Y : setwithbinop } ( f : binopmono X Y ) ( is : iscomm ( @op Y ) ) : iscomm ( @op X ) .
Proof . intros . set ( axf := pr22 f ) .  simpl in axf .  intros a b . apply ( invmaponpathsincl _ ( pr22 ( pr21 f ) ) ) . rewrite ( axf a b ) .  rewrite ( axf b a  ) . apply is . Defined .  

Opaque iscommmonob .

Notation isassocisob := isassocmonob .
Notation iscommisob := iscommmonob . 

Lemma isassocisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isassoc ( @op X ) ) : isassoc ( @op Y ) .
Proof . intros . apply ( isassocmonob ( invbinopiso f ) is ) . Defined .  

Opaque isassocisof .

Lemma iscommisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : iscomm ( @op X ) ) : iscomm ( @op Y ) .
Proof . intros .  apply ( iscommmonob ( invbinopiso f ) is ) . Defined . 

Opaque iscommisof . 

Lemma isunitisof { X Y : setwithbinop } ( f : binopiso X Y ) ( unx : X ) ( is : isunit ( @op X ) unx ) : isunit ( @op Y ) ( f unx ) .
Proof . intros . set ( axf := pr22 f ) .  split . 

intro a . change ( f unx ) with ( pr21 f unx ) . apply ( invmaponpathsweq ( pr21 ( invbinopiso f ) ) ) .  rewrite ( pr22 ( invbinopiso f ) ( pr21 f unx ) a ) . simpl . rewrite ( homotinvweqweq ( pr21 f ) unx ) .  apply ( pr21 is ) .  

intro a . change ( f unx ) with ( pr21 f unx ) . apply ( invmaponpathsweq ( pr21 ( invbinopiso f ) ) ) .  rewrite ( pr22 ( invbinopiso f ) a ( pr21 f unx ) ) . simpl . rewrite ( homotinvweqweq ( pr21 f ) unx ) .  apply ( pr22 is ) . Defined .   

Opaque isunitisof . 

Definition isunitalisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isunital ( @op X ) ) : isunital ( @op Y ) := isunitalpair ( f ( pr21 is ) ) ( isunitisof f ( pr21 is ) ( pr22 is ) ) .

Lemma isunitisob { X Y : setwithbinop } ( f : binopiso X Y ) ( uny : Y ) ( is : isunit ( @op Y ) uny ) : isunit ( @op X ) ( ( invmap f ) uny ) .
Proof . intros . set ( int := isunitisof ( invbinopiso f ) ) .  simpl . simpl in int . apply int .  apply is .  Defined .

Opaque isunitisob .

Definition isunitalisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isunital ( @op Y ) ) : isunital ( @op X ) := isunitalpair ( ( invmap f ) ( pr21 is ) ) ( isunitisob f ( pr21 is ) ( pr22 is ) ) .


Definition ismonoidopisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : ismonoidop ( @op X ) ) : ismonoidop ( @op Y ) := dirprodpair ( isassocisof f ( pr21 is ) ) ( isunitalisof f ( pr22 is ) ) . 

Definition ismonoidopisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : ismonoidop ( @op Y ) ) : ismonoidop ( @op X ) := dirprodpair ( isassocisob f ( pr21 is ) ) ( isunitalisob f ( pr22 is ) ) . 

Lemma isinvisof { X Y : setwithbinop } ( f : binopiso X Y ) ( unx : X ) ( invx : X -> X ) ( is : isinv ( @op X ) unx invx ) : isinv ( @op Y ) ( pr21 f unx ) ( funcomp ( invmap ( pr21 f ) ) ( funcomp invx ( pr21 f ) ) ) .
Proof . intros . set ( axf := pr22 f ) . set ( axinvf := pr22 ( invbinopiso f ) ) .  simpl in axf . simpl in axinvf . unfold funcomp . split .

intro a .  apply ( invmaponpathsweq ( pr21 ( invbinopiso f ) ) ) .  simpl . rewrite ( axinvf ( ( pr21 f ) (invx (invmap ( pr21 f ) a))) a ) . rewrite ( homotinvweqweq ( pr21 f ) unx ) .  rewrite ( homotinvweqweq ( pr21 f ) (invx (invmap ( pr21 f ) a)) ) . apply ( pr21 is ) .   

intro a .  apply ( invmaponpathsweq ( pr21 ( invbinopiso f ) ) ) .  simpl . rewrite ( axinvf a ( ( pr21 f ) (invx (invmap ( pr21 f ) a))) ) . rewrite ( homotinvweqweq ( pr21 f ) unx ) .  rewrite ( homotinvweqweq ( pr21 f ) (invx (invmap ( pr21 f ) a)) ) . apply ( pr22 is ) . Defined .      

Opaque isinvisof .

Definition isgroupopisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isgroupop ( @op X ) ) : isgroupop ( @op Y ) :=  tpair _ ( ismonoidopisof f is ) ( tpair _ ( funcomp ( invmap ( pr21 f ) ) ( funcomp ( grinv_is is ) ( pr21 f ) ) ) ( isinvisof f ( unel_is is ) ( grinv_is is ) ( pr22 ( pr22 is ) ) ) ) .  

Lemma isinvisob { X Y : setwithbinop } ( f : binopiso X Y ) ( uny : Y ) ( invy : Y -> Y ) ( is : isinv ( @op Y ) uny invy ) : isinv ( @op X ) ( invmap (  pr21 f ) uny ) ( funcomp ( pr21 f ) ( funcomp invy ( invmap ( pr21 f ) ) ) ) .
Proof . intros . apply ( isinvisof ( invbinopiso f ) uny invy is ) . Defined .  

Opaque isinvisob .

Definition isgroupopisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isgroupop ( @op Y ) ) : isgroupop ( @op X ) :=  tpair _ ( ismonoidopisob f is ) ( tpair _  ( funcomp ( pr21 f ) ( funcomp ( grinv_is is ) ( invmap ( pr21 f ) ) ) ) ( isinvisob f ( unel_is is ) ( grinv_is is ) ( pr22 ( pr22 is ) ) ) ) .

Definition isabmonoidopisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabmonoidop ( @op X ) ) : isabmonoidop ( @op Y ) := tpair _ ( ismonoidopisof f is ) ( iscommisof f ( commax_is is ) )  . 

Definition isabmonoidopisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabmonoidop ( @op Y ) ) : isabmonoidop ( @op X ) := tpair _ ( ismonoidopisob f is ) ( iscommisob f ( commax_is is ) )  .


Definition isabgroupopisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabgroupop ( @op X ) ) : isabgroupop ( @op Y ) := tpair _ ( isgroupopisof f is ) ( iscommisof f ( commax_is is ) )  . 

Definition isabgroupopisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabgroupop ( @op Y ) ) : isabgroupop ( @op X ) := tpair _ ( isgroupopisob f is ) ( iscommisob f ( commax_is is ) )  .

 


   


(** **** Subobjects *)

Definition issubsetwithbinop { X : hSet } ( opp : binop X ) ( A : hsubtypes X ) := forall a a' : A , A ( opp ( pr21 a ) ( pr21 a' ) ) .

Lemma isapropissubsetwithbinop { X : hSet } ( opp : binop X ) ( A : hsubtypes X ) : isaprop ( issubsetwithbinop opp A ) .
Proof .  intros .  apply impred .  intro a . apply impred . intros a' . apply ( pr22 ( A ( opp (pr21 a) (pr21 a')) ) ) . Defined .

Definition subsetswithbinop { X : setwithbinop } := total2 ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) .
Definition subsetswithbinoppair { X : setwithbinop } := tpair ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) . 
Definition subsetswithbinopconstr { X : setwithbinop } := @subsetswithbinoppair X .  
Definition pr21subsetswithbinop ( X : setwithbinop ) : @subsetswithbinop X -> hsubtypes X := @pr21 _ ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) . 
Coercion pr21subsetswithbinop : subsetswithbinop >-> hsubtypes .

Definition totalsubsetwithbinop ( X : setwithbinop ) : @subsetswithbinop X .
Proof . intros .  split with ( fun x : X => htrue ) . intros x x' .  apply tt . Defined .  


Definition carrierofasubsetwithbinop { X : setwithbinop } ( A : @subsetswithbinop X ) : setwithbinop .
Proof . intros . set ( aset := ( hSetpair ( carrier A ) ( isasetsubset ( pr21carrier A ) ( setproperty X ) ( isinclpr21carrier A ) ) ) : hSet ) . split with aset . 
set ( subopp := ( fun a a' : A => carrierpair A ( op ( pr21carrier _ a ) ( pr21carrier _ a' ) ) ( pr22 A a a' ) ) : ( A -> A -> A ) ) .  simpl . unfold binop . apply subopp .  Defined . 

Coercion carrierofasubsetwithbinop : subsetswithbinop >-> setwithbinop . 






(** **** Quotient objects *)

Definition isbinophrel { X : hSet } ( opp : binop X ) ( R : hrel X ) := forall a b c d : X , R a b -> R c d -> R ( opp a c ) ( opp b d )  .

(** Note that [ isbinophrel opp R := iscomprelrelfun2 R R opp ] . *)

Lemma isapropisbinophrel { X : hSet } ( opp : binop X ) ( R : hrel X ) : isaprop ( isbinophrel opp R ) . 
Proof . intros . apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro d . apply impred . intro rab . apply impred . intro rbc . apply ( pr22 ( R _ _ ) ) . Defined .     

Lemma isbinoptransrel { X : setwithbinop } ( R : hrel X ) ( is : istrans R )  ( is2 : forall a b c : X , R a b -> R ( op c a ) ( op c b ) ) ( is1 : forall a b c : X , R a b -> R ( op a c ) ( op b c ) )  : isbinophrel op R .
Proof . intros . intros a b c d .  intros rab rcd . set ( racbc := is1 a b c rab ) .  set ( rbcbd := is2 c d b rcd ) .  apply ( is _ _ _ racbc rbcbd ) .  Defined .  


Definition binophrel { X : setwithbinop } := total2 ( fun R : hrel X => isbinophrel ( @op X ) R ) .
Definition binophrelpair { X : setwithbinop } := tpair ( fun R : hrel X => isbinophrel ( @op X ) R ) .
Definition pr21binophrel ( X : setwithbinop ) : @binophrel X -> hrel X := @pr21 _ ( fun R : hrel X => isbinophrel ( @op X ) R ) .
Coercion pr21binophrel : binophrel >-> hrel . 

Definition binoppo { X : setwithbinop } := total2 ( fun R : po X => isbinophrel ( @op X ) R ) .
Definition binoppopair { X : setwithbinop } := tpair ( fun R : po X => isbinophrel ( @op X ) R ) .
Definition pr21binoppo ( X : setwithbinop ) : @binoppo X -> po X := @pr21 _ ( fun R : po X => isbinophrel ( @op X ) R ) .
Coercion pr21binoppo : binoppo >-> po . 

Definition binopeqrel { X : setwithbinop } := total2 ( fun R : eqrel X => isbinophrel ( @op X ) R ) .
Definition binopeqrelpair { X : setwithbinop } := tpair ( fun R : eqrel X => isbinophrel ( @op X ) R ) .
Definition pr21binopeqrel ( X : setwithbinop ) : @binopeqrel X -> eqrel X := @pr21 _ ( fun R : eqrel X => isbinophrel ( @op X ) R ) .
Coercion pr21binopeqrel : binopeqrel >-> eqrel . 

Definition setwithbinopquot { X : setwithbinop } ( R : @binopeqrel X ) : setwithbinop .
Proof . intros . split with ( setquotinset R )  .  set ( qt  := setquot R ) . set ( qtset := setquotinset R ) .  
assert ( iscomp : iscomprelrelfun2 R R op ) .   intros a b c d .  apply ( pr22 R a b c d ) . 
set ( qtmlt := setquotfun2 R R op iscomp ) .   simpl . unfold binop . apply qtmlt . Defined . 




(** **** Direct products *)

Definition setwithbinopdirprod ( X Y : setwithbinop ) : setwithbinop .
Proof . intros . split with ( setdirprod X Y ) . unfold binop .  simpl . apply ( fun xy xy' : _ => dirprodpair ( op ( pr21 xy ) ( pr21 xy' ) ) ( op ( pr22 xy ) ( pr22 xy' ) ) ) . Defined .  






(** *** Sets with two binary operations *)

(** **** General definitions *)


Definition setwith2binop := total2 ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) . 
Definition setwith2binoppair ( X : hSet ) ( opps : dirprod ( binop X ) ( binop X ) ) : setwith2binop := tpair ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) X opps .
Definition pr21setwith2binop : setwith2binop -> hSet := @pr21 _ ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) .
Coercion pr21setwith2binop : setwith2binop >-> hSet . 

Definition op1 { X : setwith2binop } : binop X := pr21 ( pr22 X ) .
Definition op2 { X : setwith2binop } : binop X := pr22 ( pr22 X ) .

Definition setwithbinop1 ( X : setwith2binop ) : setwithbinop := setwithbinoppair ( pr21 X ) ( @op1 X ) . 
Definition setwithbinop2 ( X : setwith2binop ) : setwithbinop := setwithbinoppair ( pr21 X ) ( @op2 X ) . 

Notation "x + y" := ( op1 x y ) : twobinops_scope .
Notation "x * y" := ( op2 x y ) : twobinops_scope .   


(** **** Functions compatible with a pair of binary operation ( homomorphisms ) and their properties *)

Definition istwobinopfun { X Y : setwith2binop } ( f : X -> Y ) := dirprod ( forall x x' : X , paths ( f ( op1 x x' ) ) ( op1 ( f x ) ( f x' ) ) ) ( forall x x' : X , paths ( f ( op2 x x' ) ) ( op2 ( f x ) ( f x' ) ) )  . 

Lemma isapropistwobinopfun { X Y : setwith2binop } ( f : X -> Y ) : isaprop ( istwobinopfun f ) .
Proof . intros . apply isofhleveldirprod . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . Defined .

Definition twobinopfun ( X Y : setwith2binop ) : UU0 := total2 ( fun f : X -> Y => istwobinopfun f ) .
Definition twobinopfunpair { X Y : setwith2binop } ( f : X -> Y ) ( is : istwobinopfun f ) : twobinopfun X Y := tpair _ f is . 
Definition pr21twobinopfun ( X Y : setwith2binop ) : twobinopfun X Y -> ( X -> Y ) := @pr21 _ _ . 
Coercion pr21twobinopfun : twobinopfun >-> Funclass .

Definition binop1fun { X Y : setwith2binop } ( f : twobinopfun X Y ) : binopfun ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopfunpair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr21 f ) ( pr21 ( pr22 f ) ) .

Definition binop2fun { X Y : setwith2binop } ( f : twobinopfun X Y ) : binopfun ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopfunpair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr21 f ) ( pr22 ( pr22 f ) ) .  
Lemma isasettwobinopfun  ( X Y : setwith2binop ) : isaset ( twobinopfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr21twobinopfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr21 .  intro .  apply isapropistwobinopfun . Defined . 
 

Lemma istwobinopfuncomp { X Y Z : setwith2binop } ( f : twobinopfun X Y ) ( g : twobinopfun Y Z ) : istwobinopfun ( funcomp ( pr21 f ) ( pr21 g ) ) .
Proof . intros . set ( ax1f := pr21 ( pr22 f ) ) . set ( ax2f := pr22 ( pr22 f ) ) . set ( ax1g := pr21 ( pr22 g ) ) . set ( ax2g := pr22 ( pr22 g ) ) .  split.

intros a b . unfold funcomp .  rewrite ( ax1f a b ) . rewrite ( ax1g ( pr21 f a ) ( pr21 f b ) ) .  apply idpath .
intros a b . unfold funcomp .  rewrite ( ax2f a b ) . rewrite ( ax2g ( pr21 f a ) ( pr21 f b ) ) .  apply idpath . Defined . 
 
Opaque istwobinopfuncomp . 

Definition twobinopfuncomp { X Y Z : setwith2binop } ( f : twobinopfun X Y ) ( g : twobinopfun Y Z ) : twobinopfun X Z := twobinopfunpair ( funcomp ( pr21 f ) ( pr21 g ) ) ( istwobinopfuncomp f g ) . 


Definition twobinopmono ( X Y : setwith2binop ) : UU0 := total2 ( fun f : incl X Y => istwobinopfun f ) .
Definition twobinopmonopair { X Y : setwith2binop } ( f : incl X Y ) ( is : istwobinopfun f ) : twobinopmono X Y := tpair _  f is .
Definition pr21twobinopmono ( X Y : setwith2binop ) : twobinopmono X Y -> incl X Y := @pr21 _ _ .
Coercion pr21twobinopmono : twobinopmono >-> incl .

Definition twobinopincltotwobinopfun ( X Y : setwith2binop ) : twobinopmono X Y -> twobinopfun X Y := fun f => twobinopfunpair ( pr21 ( pr21 f ) ) ( pr22 f ) .
Coercion twobinopincltotwobinopfun : twobinopmono >-> twobinopfun . 

Definition binop1mono { X Y : setwith2binop } ( f : twobinopmono X Y ) : binopmono ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopmonopair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr21 f ) ( pr21 ( pr22 f ) ) .

Definition binop2mono { X Y : setwith2binop } ( f : twobinopmono X Y ) : binopmono ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopmonopair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr21 f ) ( pr22 ( pr22 f ) ) .  

Definition twobinopmonocomp { X Y Z : setwith2binop } ( f : twobinopmono X Y ) ( g : twobinopmono Y Z ) : twobinopmono X Z := twobinopmonopair ( inclcomp ( pr21 f ) ( pr21 g ) ) ( istwobinopfuncomp f g ) . 

Definition twobinopiso ( X Y : setwith2binop ) : UU0 := total2 ( fun f : weq X Y => istwobinopfun f ) .   
Definition twobinopisopair { X Y : setwith2binop } ( f : weq X Y ) ( is : istwobinopfun f ) : twobinopiso X Y := tpair _  f is .
Definition pr21twobinopiso ( X Y : setwith2binop ) : twobinopiso X Y -> weq X Y := @pr21 _ _ .
Coercion pr21twobinopiso : twobinopiso >-> weq .

Definition twobinopisototwobinopmono ( X Y : setwith2binop ) : twobinopiso X Y -> twobinopmono X Y := fun f => twobinopmonopair ( pr21 f ) ( pr22 f ) .
Coercion twobinopisototwobinopmono : twobinopiso >-> twobinopmono . 

Definition binop1iso { X Y : setwith2binop } ( f : twobinopiso X Y ) : binopiso ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopisopair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr21 f ) ( pr21 ( pr22 f ) ) .

Definition binop2iso { X Y : setwith2binop } ( f : twobinopiso X Y ) : binopiso ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopisopair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr21 f ) ( pr22 ( pr22 f ) ) .  
Definition twobinopisocomp { X Y Z : setwith2binop } ( f : twobinopiso X Y ) ( g : twobinopiso Y Z ) : twobinopiso X Z := twobinopisopair ( weqcomp ( pr21 f ) ( pr21 g ) ) ( istwobinopfuncomp f g ) .

Lemma istwobinopfuninvmap { X Y : setwith2binop } ( f : twobinopiso X Y ) : istwobinopfun ( invmap ( pr21 f ) ) . 
Proof . intros . set ( ax1f := pr21 ( pr22 f ) ) . set ( ax2f := pr22 ( pr22 f ) ) . split .


intros a b .  apply ( invmaponpathsweq ( pr21 f ) ) .  rewrite ( homotweqinvweq ( pr21 f ) ( op1 a b ) ) .   rewrite ( ax1f (invmap (pr21 f) a) (invmap (pr21 f) b) ) .  rewrite ( homotweqinvweq ( pr21 f ) a ) .   rewrite ( homotweqinvweq ( pr21 f ) b ) .   apply idpath .
intros a b .  apply ( invmaponpathsweq ( pr21 f ) ) .  rewrite ( homotweqinvweq ( pr21 f ) ( op2 a b ) ) . rewrite ( ax2f (invmap (pr21 f) a) (invmap (pr21 f) b) ) .  rewrite ( homotweqinvweq ( pr21 f ) a ) .   rewrite ( homotweqinvweq ( pr21 f ) b ) .   apply idpath . Defined .

Opaque istwobinopfuninvmap .  

Definition invtwobinopiso { X Y : setwith2binop } ( f : twobinopiso X Y ) : twobinopiso Y X := twobinopisopair ( invweq ( pr21 f ) ) ( istwobinopfuninvmap f ) .





(** **** Transport of properties of a pair binary operations *)

Lemma isldistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isldistr ( @op1 Y ) ( @op2 Y ) ) : isldistr ( @op1 X ) ( @op2 X ) .
Proof . intros .   set ( ax1f := pr21 ( pr22 f ) ) .   set ( ax2f := pr22 ( pr22 f )  ) .   intros a b c . apply ( invmaponpathsincl _ ( pr22 ( pr21 f ) ) ) .  change ( paths ( (pr21 f) (op2 c (op1 a b)))
     ( (pr21 f) (op1 (op2 c a) (op2 c b))) ) . rewrite ( ax2f c ( op1 a b ) ) . rewrite ( ax1f a b ) .   rewrite ( ax1f ( op2 c a ) ( op2 c b ) ) . rewrite ( ax2f c a ) . rewrite ( ax2f c b ) .  apply is .  Defined . 

Opaque isldistrmonob .


Lemma isrdistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isrdistr ( @op1 Y ) ( @op2 Y ) ) : isrdistr ( @op1 X ) ( @op2 X ) .
Proof . intros .  set ( ax1f := pr21 ( pr22 f ) ) .   set ( ax2f := pr22 ( pr22 f ) ) .  intros a b c . apply ( invmaponpathsincl _ ( pr22 ( pr21 f ) ) ) . change ( paths ( (pr21 f) (op2 (op1 a b) c))
     ( (pr21 f) (op1 (op2 a c) (op2 b c))) ) .  rewrite ( ax2f ( op1 a b ) c ) . rewrite ( ax1f a b ) .   rewrite ( ax1f ( op2 a c ) ( op2 b c ) ) . rewrite ( ax2f a c ) . rewrite ( ax2f b c ) .  apply is .  Defined . 

Opaque isrdistrmonob .

Definition isdistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isdistr ( @op1 Y ) ( @op2 Y ) ) : isdistr ( @op1 X ) ( @op2 X ) := dirprodpair ( isldistrmonob f ( pr21 is ) ) ( isrdistrmonob f ( pr22 is ) ) .

Notation isldistrisob := isldistrmonob .
Notation isrdistrisob := isrdistrmonob .
Notation isdistrisob := isdistrmonob .

Lemma isldistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isldistr ( @op1 X ) ( @op2 X ) ) : isldistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isldistrisob ( invtwobinopiso f ) is ) . Defined .   

Lemma isrdistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrdistr ( @op1 X ) ( @op2 X ) ) : isrdistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isrdistrisob ( invtwobinopiso f ) is ) . Defined . 

Lemma isdistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isdistr ( @op1 X ) ( @op2 X ) ) : isdistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isdistrisob ( invtwobinopiso f ) is ) . Defined . 


Definition isrngopsisof { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrngops ( @op1 X ) ( @op2 X ) ) : isrngops ( @op1 Y ) ( @op2 Y ) := dirprodpair ( dirprodpair ( isabgroupopisof ( binop1iso f ) ( op1axs_is is ) ) ( ismonoidopisof ( binop2iso f ) ( op2axs_is is ) ) ) ( isdistrisof f ( pr22 is ) ) .

Definition isrngopsisob { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrngops ( @op1 Y ) ( @op2 Y ) ) : isrngops ( @op1 X ) ( @op2 X ) := dirprodpair ( dirprodpair ( isabgroupopisob ( binop1iso f ) ( op1axs_is is ) ) ( ismonoidopisob ( binop2iso f ) ( op2axs_is is ) ) ) ( isdistrisob f ( pr22 is ) ) .


Definition iscommrngopsisof { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : iscommrngops ( @op1 X ) ( @op2 X ) ) : iscommrngops ( @op1 Y ) ( @op2 Y ) := dirprodpair ( isrngopsisof f is ) ( iscommisof ( binop2iso f ) ( pr22 is ) ) .

Definition iscommrngopsisob { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : iscommrngops ( @op1 Y ) ( @op2 Y ) ) : iscommrngops ( @op1 X ) ( @op2 X ) := dirprodpair ( isrngopsisob f is ) ( iscommisob ( binop2iso f ) ( pr22 is ) ) .




(** **** Subobjects *)

Definition issubsetwith2binop { X : setwith2binop } ( A : hsubtypes X ) := dirprod ( forall a a' : A , A ( op1 ( pr21 a ) ( pr21 a' ) ) ) ( forall a a' : A , A ( op2 ( pr21 a ) ( pr21 a' ) ) ) .

Lemma isapropissubsetwith2binop { X : setwith2binop } ( A : hsubtypes X ) : isaprop ( issubsetwith2binop A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) .
 apply impred .  intro a . apply impred . intros a' . apply ( pr22 ( A ( op1 (pr21 a) (pr21 a')) ) ) .  apply impred .  intro a . apply impred . intros a' . apply ( pr22 ( A ( op2 (pr21 a) (pr21 a')) ) ) .  Defined .

Definition subsetswith2binop { X : setwith2binop } := total2 ( fun A : hsubtypes X => issubsetwith2binop A ) .
Definition subsetswith2binoppair { X : setwith2binop } := tpair ( fun A : hsubtypes X => issubsetwith2binop A ) . 
Definition subsetswith2binopconstr { X : setwith2binop } := @subsetswith2binoppair X .  
Definition pr21subsetswith2binop ( X : setwith2binop ) : @subsetswith2binop X -> hsubtypes X := @pr21 _ ( fun A : hsubtypes X => issubsetwith2binop A ) . 
Coercion pr21subsetswith2binop : subsetswith2binop >-> hsubtypes .

Definition totalsubsetwith2binop ( X : setwith2binop ) : @subsetswith2binop X .
Proof . intros .  split with ( fun x : X => htrue ) . split . intros x x' .  apply tt .  intros . apply tt . Defined .  


Definition carrierofsubsetwith2binop { X : setwith2binop } ( A : @subsetswith2binop X ) : setwith2binop .
Proof . intros . set ( aset := ( hSetpair ( carrier A ) ( isasetsubset ( pr21carrier A ) ( setproperty X ) ( isinclpr21carrier A ) ) ) : hSet ) . split with aset . 
set ( subopp1 := ( fun a a' : A => carrierpair A ( op1 ( pr21carrier _ a ) ( pr21carrier _ a' ) ) ( pr21 ( pr22 A ) a a' ) ) : ( A -> A -> A ) ) . 
set ( subopp2 := ( fun a a' : A => carrierpair A ( op2 ( pr21carrier _ a ) ( pr21carrier _ a' ) ) ( pr22 ( pr22 A ) a a' ) ) : ( A -> A -> A ) ) .
simpl .  apply ( dirprodpair subopp1 subopp2 ) .  Defined . 

Coercion carrierofsubsetwith2binop : subsetswith2binop >-> setwith2binop . 


(** **** Quotient objects *)

Definition is2binophrel { X : setwith2binop } ( R : hrel X ) := dirprod ( forall a b c d : X , R a b -> R c d -> R ( op1 a c ) ( op1 b d ) ) ( forall a b c d : X , R a b -> R c d -> R ( op2 a c ) ( op2 b d ) ) . 

Lemma isapropis2binophrel { X : setwith2binop } ( R : hrel X ) : isaprop ( is2binophrel R ) . 
Proof . intros . apply ( isofhleveldirprod 1 ) . apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro d . apply impred . intro rab . apply impred . intro rbc . apply ( pr22 ( R _ _ ) ) . 
apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro d . apply impred . intro rab . apply impred . intro rbc . apply ( pr22 ( R _ _ ) ) . 
Defined .    

Lemma is2binoptransrel { X : setwith2binop } ( R : hrel X ) ( is : istrans R )  ( is1l : forall a b c : X , R a b -> R ( op1 c a ) ( op1 c b ) ) ( is1r : forall a b c : X , R a b -> R ( op1 a c ) ( op1 b c ) ) ( is2l : forall a b c : X , R a b -> R ( op2 c a ) ( op2 c b ) ) ( is2r : forall a b c : X , R a b -> R ( op2 a c ) ( op2 b c ) )  : is2binophrel R .
Proof . intros . split .

intros a b c d .  intros rab rcd . set ( racbc := is1r a b c rab ) .  set ( rbcbd := is1l c d b rcd ) .  apply ( is _ _ _ racbc rbcbd ) .
intros a b c d .  intros rab rcd . set ( racbc := is2r a b c rab ) .  set ( rbcbd := is2l c d b rcd ) .  apply ( is _ _ _ racbc rbcbd ) .  Defined .  


Definition twobinophrel { X : setwith2binop } := total2 ( fun R : hrel X => is2binophrel R ) .
Definition twobinophrelpair { X : setwith2binop } := tpair ( fun R : hrel X => is2binophrel R ) .
Definition pr21twobinophrel ( X : setwith2binop ) : @twobinophrel X -> hrel X := @pr21 _ ( fun R : hrel X => is2binophrel R ) .
Coercion pr21twobinophrel : twobinophrel >-> hrel . 

Definition twobinoppo { X : setwith2binop } := total2 ( fun R : po X => is2binophrel R ) .
Definition twobinoppopair { X : setwith2binop } := tpair ( fun R : po X => is2binophrel R ) .
Definition pr21twobinoppo ( X : setwith2binop ) : @twobinoppo X -> po X := @pr21 _ ( fun R : po X => is2binophrel R ) .
Coercion pr21twobinoppo : twobinoppo >-> po . 

Definition twobinopeqrel { X : setwith2binop } := total2 ( fun R : eqrel X => is2binophrel R ) .
Definition twobinopeqrelpair { X : setwith2binop } := tpair ( fun R : eqrel X => is2binophrel R ) .
Definition pr21twobinopeqrel ( X : setwith2binop ) : @twobinopeqrel X -> eqrel X := @pr21 _ ( fun R : eqrel X => is2binophrel R ) .
Coercion pr21twobinopeqrel : twobinopeqrel >-> eqrel . 

Definition setwith2binopquot { X : setwith2binop } ( R : @twobinopeqrel X ) : setwith2binop .
Proof . intros . split with ( setquotinset R )  .  set ( qt  := setquot R ) . set ( qtset := setquotinset R ) .  
assert ( iscomp1 : iscomprelrelfun2 R R ( @op1 X ) ) .   intros a b c d .  apply ( pr21 ( pr22 R ) a b c d ) . set ( qtop1 := setquotfun2 R R ( @op1 X ) iscomp1 ) .   
assert ( iscomp2 : iscomprelrelfun2 R R ( @op2 X ) ) .   intros a b c d .  apply ( pr22 ( pr22 R ) a b c d ) . set ( qtop2 := setquotfun2 R R ( @op2 X ) iscomp2 ) .  
simpl . apply ( dirprodpair qtop1 qtop2 )  . Defined . 


(** **** Direct products *)

Definition setwith2binopdirprod ( X Y : setwith2binop ) : setwith2binop .
Proof . intros . split with ( setdirprod X Y ) . simpl . apply ( dirprodpair ( fun xy xy' : _ => dirprodpair ( op1 ( pr21 xy ) ( pr21 xy' ) ) ( op1 ( pr22 xy ) ( pr22 xy' ) ) ) ( fun xy xy' : _ => dirprodpair ( op2 ( pr21 xy ) ( pr21 xy' ) ) ( op2 ( pr22 xy ) ( pr22 xy' ) ) ) ) . Defined .  








(** ** Standard Algebraic Structures *)






(** *** Monoids *)


(** ****  Basic definitions *)



Definition monoid := total2 ( fun X : setwithbinop => ismonoidop ( @op X ) ) .
Definition monoidpair := tpair ( fun X : setwithbinop => ismonoidop ( @op X ) ) .
Definition monoidconstr := monoidpair .
Definition pr21monoid : monoid -> setwithbinop := @pr21 _ _ . 
Coercion pr21monoid : monoid >-> setwithbinop .

Definition assocax ( X : monoid ) : isassoc ( @op X ) := pr21 ( pr22 X ) .
Definition unel ( X : monoid) : X := pr21 ( pr22 ( pr22 X ) ) .
Definition lunax ( X : monoid ) : islunit ( @op X ) ( unel X ) := pr21 ( pr22 ( pr22 ( pr22 X ) ) ) .  
Definition runax ( X : monoid ) : isrunit ( @op X ) ( unel X ) := pr22 ( pr22 ( pr22 ( pr22 X ) ) ) . 


(** **** Functions betweens monoids compatible with structure ( homomorphisms ) and their properties *)


Definition ismonoidfun { X Y : monoid } ( f : X -> Y ) := dirprod ( isbinopfun f ) ( paths ( f ( unel X ) ) ( unel Y ) ) . 

Lemma isapropismonoidfun { X Y : monoid } ( f : X -> Y ) : isaprop ( ismonoidfun f ) .
Proof . intros . apply isofhleveldirprod . apply isapropisbinopfun .  apply ( setproperty Y ) . Defined .

Definition monoidfun ( X Y : monoid ) : UU0 := total2 ( fun f : X -> Y => ismonoidfun f ) .
Definition monoidfunpair { X Y : monoid } ( f : X -> Y ) ( is : ismonoidfun f ) : monoidfun X Y := tpair _ f is . 
Definition pr21monoidfun ( X Y : monoid ) : monoidfun X Y -> ( X -> Y ) := @pr21 _ _ . 

Definition monoidfuntobinopfun ( X Y : monoid ) : monoidfun X Y -> binopfun X Y := fun f => binopfunpair ( pr21 f ) ( pr21 ( pr22 f ) ) .
Coercion monoidfuntobinopfun : monoidfun >-> binopfun .  


Lemma isasetmonoidfun  ( X Y : monoid ) : isaset ( monoidfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr21monoidfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr21 .  intro .  apply isapropismonoidfun . Defined .  


Lemma ismonoidfuncomp { X Y Z : monoid } ( f : monoidfun X Y ) ( g : monoidfun Y Z ) : ismonoidfun ( funcomp ( pr21 f ) ( pr21 g ) ) .
Proof . intros . split with ( isbinopfuncomp f g ) . unfold funcomp .  rewrite ( pr22 ( pr22 f ) ) .  apply ( pr22 ( pr22 g ) ) . Defined .  

Opaque ismonoidfuncomp . 

Definition monoidfuncomp { X Y Z : monoid } ( f : monoidfun X Y ) ( g : monoidfun Y Z ) : monoidfun X Z := monoidfunpair ( funcomp ( pr21 f ) ( pr21 g ) ) ( ismonoidfuncomp f g ) . 


Definition monoidmono ( X Y : monoid ) : UU0 := total2 ( fun f : incl X Y => ismonoidfun f ) .
Definition monoidmonopair { X Y : monoid } ( f : incl X Y ) ( is : ismonoidfun f ) : monoidmono X Y := tpair _  f is .
Definition pr21monoidmono ( X Y : monoid ) : monoidmono X Y -> incl X Y := @pr21 _ _ .
Coercion pr21monoidmono : monoidmono >-> incl .

Definition monoidincltomonoidfun ( X Y : monoid ) : monoidmono X Y -> monoidfun X Y := fun f => monoidfunpair ( pr21 ( pr21 f ) ) ( pr22 f ) .
Coercion monoidincltomonoidfun : monoidmono >-> monoidfun . 

Definition monoidmonotobinopmono ( X Y : monoid ) : monoidmono X Y -> binopmono X Y := fun f => binopmonopair ( pr21 f ) ( pr21 ( pr22 f ) ) .
Coercion monoidmonotobinopmono : monoidmono >-> binopmono .  

Definition monoidmonocomp { X Y Z : monoid } ( f : monoidmono X Y ) ( g : monoidmono Y Z ) : monoidmono X Z := monoidmonopair ( inclcomp ( pr21 f ) ( pr21 g ) ) ( ismonoidfuncomp f g ) . 


Definition monoidiso ( X Y : monoid ) : UU0 := total2 ( fun f : weq X Y => ismonoidfun f ) .   
Definition monoidisopair { X Y : monoid } ( f : weq X Y ) ( is : ismonoidfun f ) : monoidiso X Y := tpair _  f is .
Definition pr21monoidiso ( X Y : monoid ) : monoidiso X Y -> weq X Y := @pr21 _ _ .
Coercion pr21monoidiso : monoidiso >-> weq .

Definition monoidisotomonoidmono ( X Y : monoid ) : monoidiso X Y -> monoidmono X Y := fun f => monoidmonopair ( pr21 f ) ( pr22 f ) .
Coercion monoidisotomonoidmono : monoidiso >-> monoidmono . 

Definition monoidisotobinopiso ( X Y : monoid ) : monoidiso X Y -> binopiso X Y := fun f => binopisopair ( pr21 f ) ( pr21 ( pr22 f ) ) .
Coercion monoidisotobinopiso : monoidiso >-> binopiso .  


Lemma ismonoidfuninvmap { X Y : monoid } ( f : monoidiso X Y ) : ismonoidfun ( invmap ( pr21 f ) ) . 
Proof . intros . split with ( isbinopfuninvmap f ) .  apply ( invmaponpathsweq ( pr21 f ) ) .  rewrite ( homotweqinvweq ( pr21 f ) ) . apply ( pathsinv0 ( pr22 ( pr22 f ) ) ) . Defined .

Opaque ismonoidfuninvmap .  

Definition invmonoidiso { X Y : monoid } ( f : monoidiso X Y ) : monoidiso Y X := monoidisopair ( invweq ( pr21 f ) ) ( ismonoidfuninvmap f ) .






(** **** Subobjects *)

Definition issubmonoid { X : monoid } ( A : hsubtypes X ) := dirprod ( issubsetwithbinop ( @op X ) A ) ( A ( unel X ) ) . 

Lemma isapropissubmonoid { X : monoid } ( A : hsubtypes X ) : isaprop ( issubmonoid A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubsetwithbinop . apply ( pr22 ( A ( unel X ) ) ) . Defined .  

Definition submonoids { X : monoid } := total2 ( fun A : hsubtypes X => issubmonoid A )  . 
Definition submonoidpair { X : monoid } := tpair ( fun A : hsubtypes X => issubmonoid A ) . 
Definition submonoidconstr { X : monoid } := @submonoidpair X . 
Definition pr21submonoids ( X : monoid ) : @submonoids X -> hsubtypes X := @pr21 _ _ . 

Definition totalsubmonoid  ( X : monoid ) : @submonoids X .
Proof . intro . split with ( fun x : _ => htrue ) . split . intros x x' . apply tt . apply tt . Defined .   

Definition submonoidstosubsetswithbinop ( X : monoid ) : @submonoids X -> @subsetswithbinop X := fun A : _ => subsetswithbinoppair ( pr21 A ) ( pr21 ( pr22 A ) ) . 
Coercion  submonoidstosubsetswithbinop : submonoids >-> subsetswithbinop .

Lemma ismonoidcarrier { X : monoid } ( A : @submonoids X ) : ismonoidop ( @op A ) . 
Proof . intros . split .  intros a a' a'' .  apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) . simpl .  apply ( assocax X ) . split with ( carrierpair _ ( unel X ) ( pr22 ( pr22 A ) ) ) .   split . simpl . intro a . apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply ( lunax X ) .  intro a . apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply ( runax X ) . Defined . 

Definition carrierofsubmonoid { X : monoid } ( A : @submonoids X ) : monoid .
Proof . intros . split with A . apply ismonoidcarrier . Defined . 

Coercion carrierofsubmonoid : submonoids >-> monoid . 




(** **** Quotient objects *)

Lemma isassocquot { X : monoid } ( R : @binopeqrel X ) : isassoc ( @op ( setwithbinopquot R ) ) . 
Proof . intros . intros a b c .  apply  ( setquotuniv3prop R ( fun x x' x'' : setwithbinopquot R  => hProppair _ ( setproperty ( setwithbinopquot R ) ( op ( op x x' ) x'' ) ( op x ( op x' x'' )) ) ) ) .  intros x x' x'' . apply ( maponpaths ( setquotpr R ) ( assocax X x x' x'' ) ) .  Defined . 

Opaque isassocquot .
    

Lemma isunitquot { X : monoid } ( R : @binopeqrel X ) : isunit ( @op ( setwithbinopquot R ) ) ( setquotpr R ( pr21 ( pr22 ( pr22 X ) ) ) ) .
Proof . intros .  set ( qun := setquotpr R ( pr21 ( pr22 ( pr22 X ) ) ) ) . set ( qsetwithop := setwithbinopquot R ) .  split .  

intro x . apply ( setquotunivprop R ( fun x => @eqset qsetwithop ( ( @op qsetwithop ) qun x ) x ) ) .  simpl . intro x0 .   apply ( maponpaths ( setquotpr R ) ( lunax X x0 ) ) . 

intro x . apply ( setquotunivprop R ( fun x => @eqset qsetwithop ( ( @op qsetwithop ) x qun ) x ) ) .  simpl . intro x0 . apply ( maponpaths ( setquotpr R ) ( runax X x0 ) ) . Defined .

Opaque isunitquot . 


Definition ismonoidquot { X : monoid } ( R : @binopeqrel X ) : ismonoidop ( @op ( setwithbinopquot R ) ) := tpair _ ( isassocquot R ) ( tpair _ ( setquotpr R ( pr21 ( pr22 ( pr22 X ) ) ) ) ( isunitquot R ) ) .  

Definition monoidquot { X : monoid } ( R : @binopeqrel X ) : monoid .
Proof . intros . split with ( setwithbinopquot R ) . apply ismonoidquot . Defined . 


(** **** Direct products *)

Lemma isassocdirprod ( X Y : monoid ) : isassoc ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros .  simpl . intros xy xy' xy'' .  simpl . apply pathsdirprod .  apply ( assocax X ) .  apply ( assocax Y ) .  Defined . 

Opaque isassocdirprod .

Lemma isunitindirprod ( X Y : monoid ) : isunit ( @op ( setwithbinopdirprod X Y ) ) ( dirprodpair ( unel X ) ( unel Y ) ) .
Proof . split . 

intro xy . destruct xy as [ x y ] . simpl . apply pathsdirprod .  apply ( lunax X ) .  apply ( lunax Y ) . 
intro xy .  destruct xy as [ x y ] . simpl . apply pathsdirprod .  apply ( runax X ) .  apply ( runax Y ) . Defined . 

Opaque isunitindirprod . 

Definition ismonoiddirprod ( X Y : monoid ) : ismonoidop ( @op ( setwithbinopdirprod X Y ) ) := tpair _ ( isassocdirprod X Y ) ( tpair _ ( dirprodpair ( unel X ) ( unel Y ) ) ( isunitindirprod X Y ) ) .  

Definition monoiddirprod ( X Y : monoid ) : monoid .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply ismonoiddirprod . Defined .  






(** *** Abelian ( commutative ) monoids *)


(** **** Basic definitions *)


Definition abmonoid := total2 ( fun X : setwithbinop =>  isabmonoidop ( @op X ) ) .
Definition abmonoidpair := tpair ( fun X : setwithbinop =>  isabmonoidop ( @op X ) ) .
Definition abmonoidconstr := abmonoidpair .

Definition abmonoidtomonoid : abmonoid -> monoid := fun X : _ => monoidpair ( pr21 X ) ( pr21 ( pr22 X ) ) .
Coercion abmonoidtomonoid : abmonoid >-> monoid .

Definition commax ( X : abmonoid ) : iscomm ( @op X ) := pr22 ( pr22 X ) .


(** **** Subobjects *)

Definition subabmonoids { X : abmonoid } := @submonoids X .
Identity Coercion id_subabmonoids : subabmonoids >-> submonoids . 

Lemma isabmonoidcarrier  { X : abmonoid } ( A : @submonoids X ) : isabmonoidop ( @op A ) .
Proof . intros . split with ( ismonoidcarrier A ) .   intros a a' .  apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply ( pr22 ( pr22 X ) ) . Defined .

Opaque isabmonoidcarrier .  

Definition carrierofsubabmonoid { X : abmonoid } ( A : @subabmonoids X ) : abmonoid .
Proof . intros . unfold subabmonoids in A . split with A . apply isabmonoidcarrier . Defined . 

Coercion carrierofsubabmonoid : subabmonoids >-> abmonoid . 




(** **** Quotient objects *)


Lemma isabmonoidquot { X : abmonoid } ( R : @binopeqrel X ) : isabmonoidop ( @op ( setwithbinopquot R ) ) .
Proof . intros . split with ( ismonoidquot R ) .  set ( X0 := setwithbinopquot R ) . intros x x' .  apply ( setquotuniv2prop R ( fun x x' : X0 => hProppair _ ( setproperty X0 ( op x x') ( op x' x) ) ) ) . intros x0 x0' .  apply ( maponpaths ( setquotpr R ) ( ( commax X ) x0 x0' ) ) . Defined .

Opaque isabmonoidquot .

Definition abmonoidquot { X : abmonoid } ( R : @binopeqrel X ) : abmonoid .
Proof . intros . split with  ( setwithbinopquot R )  . apply isabmonoidquot . Defined .  


(** **** Direct products *)

Lemma isabmonoiddirprod ( X Y : abmonoid ) : isabmonoidop ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . split with ( ismonoiddirprod X Y ) . intros xy xy' . destruct xy as [ x y ] . destruct xy' as [ x' y' ] .  simpl .  apply pathsdirprod .  apply ( commax X ) .  apply ( commax Y ) .  Defined .

Opaque isabmonoiddirprod . 

Definition abmonoiddirprod ( X Y : abmonoid ) : abmonoid .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isabmonoiddirprod .  Defined . 




(** **** Monoid of fractions of an abelian monoid 

Note : the following construction uses onbly associativity and commutativity of the [ abmonoid ] operations but does not use the unit element . *)

Open Scope addoperation_scope .

Definition abmonoidfracopint ( X : abmonoid ) ( A : @submonoids X ) : binop ( dirprod X A ) := @op ( setwithbinopdirprod X A ) .

Definition  hrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : hrel ( dirprod X A ) :=  fun xa yb : dirprod X A => ishinh ( total2 ( fun a0 : A =>  paths ( ( ( pr21 xa ) + ( pr21 ( pr22 yb ) ) ) + ( pr21 a0 ) )  ( ( ( pr21 yb ) + ( pr21 ( pr22 xa ) ) + ( pr21 a0 ) ) ) ) ) . 

Lemma isbinophrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : @isbinophrel _ ( @op ( setwithbinopdirprod X A ) ) ( hrelabmonoidfrac X A ) . 
Proof . intros . set ( rer := abmonoidoprer ( pr22 X ) ) .  intros a b c d .  simpl . apply hinhfun2 .  destruct a as [ a a' ] . destruct a' as [ a' isa' ] . destruct b as [ b b' ] . destruct b' as [ b' isb' ] . destruct c as [ c c' ] . destruct c' as [ c' isc' ] . destruct d as [ d d' ] . destruct d' as [ d' isd' ] . intros ax ay .  destruct ax as [ a1 eq1 ] . destruct ay as [ a2 eq2 ] . split with ( @op A  a1 a2 ) .  destruct a1 as [ a1 aa1 ] . destruct a2 as [ a2 aa2 ] . simpl in *.  rewrite ( rer a c b' d' ) . rewrite ( rer b d a' c' ) . rewrite ( rer ( a + b' ) ( c + d' ) a1 a2 ) .  rewrite ( rer ( b + a' ) ( d + c' ) a1 a2 ) . destruct eq1 . destruct eq2 . apply idpath . Defined .

Opaque isbinophrelabmonoidfrac .
 
Lemma iseqrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : iseqrel ( hrelabmonoidfrac X A ) .
Proof . intros . set ( assoc := assocax X ) . set ( comm := commax X ) . set ( R := hrelabmonoidfrac X A ) .

assert ( symm : issymm R ) . intros xa yb .  unfold R . simpl . apply hinhfun .  intro eq1 . destruct eq1 as [ x1 eq1 ] . split with x1 . destruct x1 as [ x1 isx1 ] .  simpl . apply ( pathsinv0 eq1 ) . 

assert ( trans : istrans R ) .  unfold istrans . intros ab cd ef .  simpl . apply hinhfun2 .   destruct ab as [ a b ] . destruct cd as [ c d ] . destruct ef as [ e f ] .   destruct b as [ b isb ] . destruct d as [ d isd ] .  destruct f as [ f isf ] .   intros eq1 eq2 .  destruct eq1 as [ x1 eq1 ] . destruct eq2 as [ x2 eq2 ] . simpl in * . split with ( @op A ( tpair _ d isd ) ( @op A x1 x2 ) ) .  destruct x1 as [ x1 isx1 ] . destruct x2 as [ x2 isx2 ] . destruct A as [ A ax ] . simpl in * .  rewrite ( assoc a f ( d + ( x1 + x2 ) ) ) .  rewrite ( comm f ( d + ( x1 + x2 ) ) ) .  destruct ( assoc a ( d + ( x1 + x2 ) ) f ) .  destruct ( assoc a d ( x1 + x2 ) )  .  destruct ( assoc ( a + d ) x1 x2 )  . rewrite eq1 . rewrite ( comm x1 x2 ) .   rewrite ( assoc e b ( d + ( x2 + x1 ) ) ) .  rewrite ( comm b ( d + ( x2 + x1 ) ) ) .  destruct ( assoc e ( d + ( x2 + x1 ) ) b ) . destruct ( assoc e d ( x2 + x1 ) )  . destruct ( assoc ( e + d ) x2 x1 ) .  destruct eq2 . rewrite ( assoc ( c + b ) x1 x2 ) .  rewrite ( assoc ( c + f ) x2 x1 )  . rewrite ( comm x1 x2 ) .  rewrite ( assoc ( c + b ) ( x2 + x1 ) f ) .  rewrite ( assoc ( c + f ) ( x2 + x1 ) b ) .   rewrite ( comm ( x2 + x1 ) f ) .  rewrite ( comm ( x2 + x1 ) b ) . destruct ( assoc ( c + b ) f ( x2 + x1 ) ) .  destruct ( assoc ( c + f ) b ( x2 + x1 ) ) . rewrite ( assoc c b f ) .  rewrite ( assoc c f b ) . rewrite ( comm b f ) .  apply idpath . 

assert ( refl : isrefl R ) . intro xa .  simpl .  apply hinhpr . split with ( pr22 xa ) . apply idpath .  

apply ( iseqrelconstr trans refl symm ) . Defined .

Opaque iseqrelabmonoidfrac .  



Definition eqrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : eqrel ( dirprod X A ) := eqrelpair ( hrelabmonoidfrac X A ) ( iseqrelabmonoidfrac X A ) .

Definition abmonoidfracop ( X : abmonoid ) ( A : @submonoids X ) : binop ( setquot ( hrelabmonoidfrac X A ) ) := setquotfun2 ( hrelabmonoidfrac X A ) ( eqrelabmonoidfrac X A ) ( abmonoidfracopint X A ) ( isbinophrelabmonoidfrac X A ) . 

Definition binopeqrelabmonoidfrac ( X : abmonoid ) ( A : @subabmonoids X ) : @binopeqrel ( abmonoiddirprod X A ) := @binopeqrelpair ( setwithbinopdirprod X A ) ( eqrelabmonoidfrac X A ) ( isbinophrelabmonoidfrac X A ) .   

Definition abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : abmonoid := abmonoidquot ( binopeqrelabmonoidfrac X A ) . 

Definition prabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : X -> A -> abmonoidfrac X A := fun ( x : X ) ( a : A ) => setquotpr ( eqrelabmonoidfrac X A ) ( dirprodpair x a ) . 

Lemma invertibilityinabmonoidfrac  ( X : abmonoid ) ( A : @submonoids X ) : forall a a' : A , isinvertible ( @op ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr21 a ) a' ) .  
Proof . intros . set ( R := eqrelabmonoidfrac X A ) .   unfold isinvertible .  

assert ( isl : islinvertible ( @op ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr21 a ) a' ) ) . unfold islinvertible .  set ( f := fun x0 : abmonoidfrac X A => prabmonoidfrac X A (pr21 a) a' + x0 ) . set ( g := fun x0 : abmonoidfrac X A => prabmonoidfrac X A (pr21 a' ) a + x0 ) .
assert ( egf : forall x0 : _ , paths ( g ( f x0 ) ) x0 ) . apply ( setquotunivprop R ( fun x0 : abmonoidfrac X A => eqset (g (f x0)) x0 ) ) .  intro xb . simpl . apply ( iscompsetquotpr R ( @dirprodpair X A ( ( pr21 a' ) + ( ( pr21 a ) + ( pr21 xb ) ) ) ( ( @op A ) a ( ( @op A ) a' ( pr22 xb ) ) ) ) ) .   simpl .  apply hinhpr .  split with ( unel A ) .  unfold pr21carrier . simpl . set  ( e := assocax X ( pr21 a ) ( pr21 a' ) ( pr21 ( pr22 xb ) ) ) . simpl in e . destruct e .  set ( e := assocax X ( pr21 xb ) ( pr21 a + pr21 a' ) ( pr21 ( pr22 xb ) ) ) . simpl in e .  destruct e . set ( e := assocax X ( pr21 a' ) ( pr21 a ) ( pr21 xb ) ) . simpl in e .  destruct e . set ( e := commax X ( pr21 a ) ( pr21 a' ) ) . simpl in e . destruct e .  set ( e := commax X ( pr21 a + pr21 a' ) ( pr21 xb ) ) . simpl in e . destruct e . apply idpath . 
assert ( efg : forall x0 : _ , paths ( f ( g x0 ) ) x0 ) .  apply ( setquotunivprop R ( fun x0 : abmonoidfrac X A => eqset (f (g x0)) x0 ) ) .  intro xb . simpl . apply ( iscompsetquotpr R ( @dirprodpair X A ( ( pr21 a ) + ( ( pr21 a' ) + ( pr21 xb ) ) ) ( ( @op A ) a' ( ( @op A ) a ( pr22 xb ) ) ) ) ) .   simpl .  apply hinhpr .  split with ( unel A ) .  unfold pr21carrier . simpl . set  ( e := assocax X ( pr21 a' ) ( pr21 a ) ( pr21 ( pr22 xb ) ) ) . simpl in e . destruct e .  set ( e := assocax X ( pr21 xb ) ( pr21 a' + pr21 a ) ( pr21 ( pr22 xb ) ) ) . simpl in e .  destruct e . set ( e := assocax X ( pr21 a ) ( pr21 a' ) ( pr21 xb ) ) . simpl in e .  destruct e . set ( e := commax X ( pr21 a' ) ( pr21 a ) ) . simpl in e . destruct e .  set ( e := commax X ( pr21 a' + pr21 a ) ( pr21 xb ) ) . simpl in e . destruct e . apply idpath .
apply ( gradth _ _ egf efg ) . 

apply ( dirprodpair isl ( weqlinvertiblerinvertible ( @op ( abmonoidfrac X A ) ) ( commax ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr21 a ) a' ) isl ) ) . 
Defined .  



(** **** Monoid of fractions in the case when elements of the localziation submonoid are cancellable *)

Definition  hrel0abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : hrel ( dirprod X A ) :=  fun xa yb : setdirprod X A => eqset ( ( pr21 xa ) + ( pr21 ( pr22 yb ) ) )  ( ( pr21 yb ) + ( pr21 ( pr22 xa ) ) ) .

Lemma weqhrelhrel0abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancellable ( @op X ) ( pr21carrier _ a ) ) ( xa xa' : dirprod X A ) : weq ( eqrelabmonoidfrac X A xa xa' ) ( hrel0abmonoidfrac X A xa xa' ) .
Proof . intros .  unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl .  apply weqimplimpl .  

apply ( @hinhuniv _ ( eqset (pr21 xa + pr21 (pr22 xa')) (pr21 xa' + pr21 (pr22 xa)) ) ) .  intro ae .  destruct ae as [ a eq ] .  apply ( invmaponpathsincl _ ( iscanc a ) _ _ eq ) . 
intro eq . apply hinhpr . split with ( unel A ) . rewrite ( runax X )  .  rewrite ( runax X ) .  apply eq . apply ( isapropishinh _ ) .  apply ( setproperty X ) .   Defined .



Lemma isinclprabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancellable ( @op X ) ( pr21carrier _ a ) ) : forall a' : A , isincl ( fun x => prabmonoidfrac X A x a' ) .
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) .  apply ( setproperty ( abmonoidfrac X A ) ) .  intros x x' .   intro e .  set ( e' := invweq ( weqpathsinsetquot ( eqrelabmonoidfrac X A ) ( dirprodpair x a' ) ( dirprodpair x' a' ) )  e ) . set ( e'':= weqhrelhrel0abmonoidfrac X A iscanc ( dirprodpair _ _ ) ( dirprodpair _ _ ) e' ) . simpl in e'' . apply ( invmaponpathsincl _ ( iscanc a' ) ) . apply e'' .  Defined . 


Lemma isdeceqabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancellable ( @op X ) ( pr21carrier _ a ) ) ( is : isdeceq X ) : isdeceq ( abmonoidfrac X A ) .
Proof . intros . apply ( isdeceqsetquot ( eqrelabmonoidfrac X A ) ) .   intros xa xa' .  apply ( isdecpropweqb ( weqhrelhrel0abmonoidfrac X A iscanc xa xa' ) ) . apply isdecpropif  . unfold isaprop . simpl . set ( int := setproperty X (pr21 xa + pr21 (pr22 xa')) (pr21 xa' + pr21 (pr22 xa))) . simpl in int . apply int . unfold hrel0abmonoidfrac . unfold eqset .   simpl . apply ( is _ _ ) . Defined . 




Close Scope addoperation_scope . 



(** *** Groups *)

(** **** Basic definitions *)




Definition gr := total2 ( fun X : setwithbinop =>  isgroupop ( @op X ) ) .
Definition grpair := tpair ( fun X : setwithbinop => isgroupop ( @op X ) ) .
Definition grconstr := grpair .
Definition grtomonoid : gr -> monoid := fun X : _ => monoidpair ( pr21 X ) ( pr21 ( pr22 X ) ) . 
Coercion grtomonoid : gr >-> monoid .

Definition grinv ( X : gr ) : X -> X := pr21 ( pr22 ( pr22 X ) ) .
Definition grlinvax ( X : gr ) : islinv ( @op X ) ( unel X ) ( grinv X ) := pr21 ( pr22 ( pr22 ( pr22 X ) ) ) .
Definition grrinvax ( X : gr ) : isrinv ( @op X ) ( unel X ) ( grinv X ) := pr22 ( pr22 ( pr22 ( pr22 X ) ) ) .

Lemma monoidfuninvtoinv { X Y : gr } ( f : monoidfun X Y ) ( x : X ) : paths ( f ( grinv X x ) ) ( grinv Y ( f x ) ) .
Proof . intros . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is ( pr22 Y ) ( f x ) ) ) ) . simpl . change ( paths (op (pr21 f (grinv X x)) (pr21 f x))
     (op (grinv Y (pr21 f x)) (pr21 f x)) ) . rewrite ( grlinvax Y ( pr21 f x) ) .  destruct ( pr21 ( pr22 f ) (grinv X x) x ) .  rewrite ( grlinvax X x ) .   apply ( pr22 ( pr22 f ) ) . Defined .  


(** **** Subobjects *)

Definition issubgr { X : gr } ( A : hsubtypes X ) := dirprod ( issubmonoid A ) ( forall x : X , A x -> A ( grinv X x ) ) . 

Lemma isapropissubgr { X : gr } ( A : hsubtypes X ) : isaprop ( issubgr A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubmonoid . apply impred . intro x .   apply impred . intro a . apply ( pr22 (A ( grinv X x)) ) . Defined . 


 

Definition subgrs { X : gr } := total2 ( fun A : hsubtypes X => issubgr A ) .
Definition subgrpair { X : gr } := tpair ( fun A : hsubtypes X => issubgr A ) . 
Definition subgrconstr { X : gr } := @subgrpair X .  
Definition subgrstosubmonoids ( X : gr ) : @subgrs X -> @submonoids X := fun A : _ => submonoidpair ( pr21 A ) ( pr21 ( pr22 A ) ) . 
Coercion subgrstosubmonoids : subgrs >-> submonoids .

Lemma isinvoncarrier { X : gr } ( A : @subgrs X ) : isinv ( @op A ) ( unel A ) ( fun a : A => carrierpair _ ( grinv X ( pr21 a ) ) ( pr22 ( pr22 A ) ( pr21 a ) ( pr22 a ) ) ) .
Proof . intros . split .

intro a .  apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply ( grlinvax X ( pr21 a ) ) .  
intro a .  apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply ( grrinvax X ( pr21 a ) ) . Defined .  

Definition isgrcarrier { X : gr } ( A : @subgrs X ) : isgroupop ( @op A ) := tpair _ ( ismonoidcarrier A ) ( tpair _ ( fun a : A => carrierpair _ ( grinv X ( pr21 a ) ) ( pr22 ( pr22 A ) ( pr21 a ) ( pr22 a ) ) ) ( isinvoncarrier A ) ) . 

Definition carrierofasubgr { X : gr } ( A : @subgrs X ) : gr .
Proof . intros . split with A . apply ( isgrcarrier A ) . Defined .   


Coercion carrierofasubgr : subgrs >-> gr . 



(** **** Quotient objects *)

Lemma grquotinvcomp { X : gr } ( R : @binopeqrel X ) : iscomprelrelfun R R (grinv X) .
Proof . intros . unfold iscomprelrelfun .   intros x x' r .  destruct R as [ R isb ] . destruct R as [ R iseq ] .  destruct iseq as [ ispo0 symm0 ] . destruct ispo0 as [ trans0 refl0 ] . unfold isbinophrel in isb .   set ( r0 :=  isb _ _ _ _ ( isb _ _ _ _ ( refl0 ( grinv X x' ) ) r ) ( refl0 ( grinv X x ) ) ) .   rewrite ( grlinvax X x' ) in r0 .  rewrite ( assocax X ( grinv X x' ) x ( grinv X x ) ) in r0 .  rewrite ( grrinvax X x ) in r0 . rewrite ( lunax X _ ) in r0 . rewrite ( runax X _ ) in r0 .   apply ( symm0 _ _ r0 ) .  Defined . 

Opaque grquotinvcomp . 

Definition invongrquot { X : gr } ( R : @binopeqrel X ) : setquot R -> setquot R := setquotfun R R ( grinv X ) ( grquotinvcomp R ) .
  
Lemma isinvongrquot { X : gr } ( R : @binopeqrel X ) : isinv ( @op ( setwithbinopquot R ) ) ( setquotpr R ( unel X ) ) ( invongrquot R ) . 
Proof . intros . split .

unfold islinv .  apply ( setquotunivprop R ( fun x : setwithbinopquot R, eqset (@op ( setwithbinopquot R ) (invongrquot R x) x) (setquotpr R (unel X)) ) ) .  intro x . apply ( @maponpaths _ _ ( setquotpr R ) ( @op X ( grinv X x ) x ) ( unel X ) ) .  apply ( grlinvax X ) . 

unfold isrinv .  apply ( setquotunivprop R ( fun x : setwithbinopquot R, eqset (@op ( setwithbinopquot R ) x (invongrquot R x) ) (setquotpr R (unel X)) ) ) .  intro x . apply ( @maponpaths _ _ ( setquotpr R ) ( @op X x ( grinv X x ) ) ( unel X ) ) .  apply ( grrinvax X ) . Defined .

Opaque isinvongrquot . 

Definition isgrquot { X : gr } ( R : @binopeqrel X ) : isgroupop ( @op ( setwithbinopquot R ) ) := tpair _ ( ismonoidquot R ) ( tpair _ ( invongrquot R ) ( isinvongrquot R ) ) . 

Definition grquot { X : gr } ( R : @binopeqrel X ) : gr .
Proof . intros . split with ( setwithbinopquot R ) . apply isgrquot . Defined .  


(** **** Direct products *)


Lemma isgrdirprod ( X Y : gr ) : isgroupop ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . split with ( ismonoiddirprod X Y ) .  split with ( fun xy : _ => dirprodpair ( grinv X ( pr21 xy ) ) ( grinv Y ( pr22 xy ) ) ) .  split .

intro xy . destruct xy as [ x y ] .  unfold unel_is . simpl . apply pathsdirprod . apply ( grlinvax X x ) .  apply ( grlinvax Y y ) . 
intro xy . destruct xy as [ x y ] .  unfold unel_is . simpl .  apply pathsdirprod . apply ( grrinvax X x ) .  apply ( grrinvax Y y ) . Defined .

Definition grdirprod ( X Y : gr ) : gr .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isgrdirprod . Defined .   




(** *** Abelian groups *)


(** **** Basic definitions *)


Definition abgr := total2 ( fun X : setwithbinop =>  isabgroupop ( @op X ) ) .
Definition abgrpair ( X : setwithbinop ) ( is : isabgroupop ( @op X ) ) : abgr  := tpair ( fun X : setwithbinop =>  isabgroupop ( @op X ) ) X is .
Definition abgrconstr ( X : abmonoid ) ( inv0 : X -> X ) ( is : isinv ( @op X ) ( unel X ) inv0 ) : abgr := abgrpair X ( dirprodpair ( isgroupoppair ( pr22 X ) ( tpair _ inv0 is ) ) ( commax X ) ) .
Definition abgrtogr : abgr -> gr := fun X : _ => grpair ( pr21 X ) ( pr21 ( pr22 X ) ) . 
Coercion abgrtogr : abgr >-> gr .

Definition abgrtoabmonoid : abgr -> abmonoid := fun X : _ => abmonoidpair ( pr21 X ) ( dirprodpair ( pr21 ( pr21 ( pr22 X ) ) ) ( pr22 ( pr22 X ) ) )  .  
Coercion abgrtoabmonoid : abgr >-> abmonoid .


(** **** Subobjects *)


Definition subabgrs { X : abgr } := @subgrs X .
Identity Coercion id_subabgrs : subabgrs >-> subgrs .

Lemma isabgrcarrier { X : abgr } ( A : @subgrs X ) : isabgroupop ( @op A ) .
Proof . intros . split with ( isgrcarrier A ) . apply ( pr22 ( @isabmonoidcarrier X A ) ) .  Defined . 

Definition carrierofasubabgr { X : abgr } ( A : @subabgrs X ) : abgr .
Proof . intros . split with A . apply isabgrcarrier .  Defined . 

Coercion carrierofasubabgr : subabgrs >-> abgr . 



(** **** Quotient objects *)

Lemma isabgrquot { X : abgr } ( R : @binopeqrel X ) : isabgroupop ( @op ( setwithbinopquot R ) ) .
Proof . intros . split with ( isgrquot R ) . apply ( pr22 ( @isabmonoidquot X R ) ) .  Defined . 


Definition abgrquot { X : abgr } ( R : @binopeqrel X ) : abgr .
Proof . intros . split with ( setwithbinopquot R ) . apply isabgrquot . Defined . 


(** **** Direct products *)

Lemma isabgrdirprod ( X Y : abgr ) : isabgroupop ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . split with ( isgrdirprod X Y ) .  apply ( pr22 ( isabmonoiddirprod X Y ) ) .  Defined . 

Definition abgrdirprod ( X Y : abgr ) : abgr .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isabgrdirprod . Defined . 


(** **** Abelian group of fractions of an abelian unitary monoid *)

Open Scope addoperation_scope . 

Definition hrelabgrfrac ( X : abmonoid ) : hrel ( dirprod X X ) := fun xx' xx'' => ishinh ( total2 ( fun x0 : X =>  paths ( ( ( pr21 xx' ) + ( pr22 xx'' ) ) + x0 )  ( ( ( pr21 xx'' ) + ( pr22 xx' ) ) + x0 ) ) ) . 

Definition hrelabgrfrac' ( X : abmonoid ) : hrel ( dirprod X X ) :=  fun xx' xx'' => eqrelabmonoidfrac X ( totalsubmonoid X ) ( dirprodpair ( pr21 xx' ) ( carrierpair ( fun x : X => htrue ) ( pr22 xx' ) tt ) ) ( dirprodpair ( pr21 xx'' ) ( carrierpair ( fun x : X => htrue ) ( pr22 xx'' ) tt ) ) .

Lemma hrelabmonoidfrac_l ( X : abmonoid ) : paths ( hrelabgrfrac' X ) ( hrelabgrfrac X ) .
Proof . intros . apply funextsec . intro xx' . apply funextsec . intro xx'' . apply uahp .

intro r' . unfold hrelabgrfrac . apply ( fun f => @hinhfun _ (total2 (fun x0 : X => paths (pr21 xx' + pr22 xx'' + x0) (pr21 xx'' + pr22 xx' + x0))) f r' ) .      simpl . intro tt0 .  destruct tt0 as [ xx0 is0 ]  . split with ( pr21 xx0 ) . apply is0 .   
intro r .  unfold hrelabgrfrac' . simpl .  apply ( fun f => @hinhfun _ _ f r ) .  intro tt0 .  destruct tt0 as [ xx0 is0 ]  . split with ( carrierpair ( fun x : X => htrue ) xx0 tt ) . apply is0 . Defined .

Lemma iseqrelabgrfrac ( X : abmonoid ) : iseqrel ( hrelabgrfrac X ) .
Proof . intro . destruct ( hrelabmonoidfrac_l X ) .  apply ( iseqrelconstr ) . intros xx' xx'' xx''' . intros r1 r2 . apply ( eqreltrans ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ _ r1 r2 ) . intro xx. apply ( eqrelrefl ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ ) . intros xx xx' .  intro r . apply ( eqrelsymm ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ r ) . Defined .

Opaque iseqrelabgrfrac . 

Definition eqrelabgrfrac ( X : abmonoid ) : @eqrel ( abmonoiddirprod X X ) := eqrelpair _ ( iseqrelabgrfrac X ) .

Lemma isbinophrelabgrfrac ( X : abmonoid ) : isbinophrel ( @op ( abmonoiddirprod X X ) ) ( hrelabgrfrac X ) .
Proof . intro .  destruct ( hrelabmonoidfrac_l X ) .  intros a b c d . intros r1 r2 .  apply ( isbinophrelabmonoidfrac X ( totalsubmonoid X ) _ _ _ _ r1 r2 ) . Defined .  

Opaque isbinophrelabgrfrac .

Definition binopeqrelabgrfrac ( X : abmonoid ) : @binopeqrel ( abmonoiddirprod X X ) := binopeqrelpair ( eqrelabgrfrac X ) ( isbinophrelabgrfrac X ) .

Definition abgrfraccarrier ( X : abmonoid ) : abmonoid := @abmonoidquot ( abmonoiddirprod X X ) ( binopeqrelabgrfrac X ) .

Definition abgrfracinvint ( X : abmonoid ) :  dirprod X X -> dirprod X X := fun xs : _ => dirprodpair ( pr22 xs ) ( pr21 xs ) . 

Lemma  abgrfracinvcomp ( X : abmonoid ) : iscomprelrelfun ( hrelabgrfrac X ) ( eqrelabgrfrac X ) ( abgrfracinvint X ) .   
Proof . intros . unfold iscomprelrelfun . unfold eqrelabgrfrac . unfold hrelabgrfrac .   unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl . intros xs xs' .  apply ( hinhfun ) .   intro tt0 . 
set ( x := pr21 xs ) .  set ( s := pr22 xs ) . set ( x' := pr21 xs' ) . set ( s' := pr22 xs' ) . split with ( pr21 tt0 ) . destruct tt0 as [ a eq ] .  change ( paths ( s + x' + a ) ( s' + x + a ) ) .  apply pathsinv0 . simpl . set  ( e := commax X s' x ) . simpl in e . rewrite e . clear e . set  ( e := commax X s x' ) . simpl in e . rewrite e .    clear e.  apply eq . Defined . 

Opaque abgrfracinvcomp . 

Definition abgrfracinv ( X : abmonoid ) : abgrfraccarrier X -> abgrfraccarrier X := setquotfun ( hrelabgrfrac X ) ( eqrelabgrfrac X ) ( abgrfracinvint X ) ( abgrfracinvcomp X ) .   

Lemma abgrfracisinv ( X : abmonoid ) : isinv ( @op ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) . 
Proof . intros . set ( R := eqrelabgrfrac X ) . 

assert ( isl : islinv ( @op ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) ) .  unfold islinv . apply ( setquotunivprop R  ( fun x : abgrfraccarrier X => eqset (abgrfracinv X x + x) (unel (abgrfraccarrier X)) ) ) . intro xs . set ( x := pr21 xs ) .  set ( s := pr22 xs ) . apply ( iscompsetquotpr R ( @op ( abmonoiddirprod X X  ) ( abgrfracinvint X xs ) xs ) ( unel _ ) ) .  simpl . apply hinhpr . split with ( unel X ) . change ( paths ( s + x + ( unel X ) + ( unel X ) ) ( ( unel X ) + ( x + s ) + ( unel X ) ) ) .   destruct ( commax X x s ) .  destruct ( commax X ( unel X ) ( x + s ) ) . apply idpath .

apply ( dirprodpair isl ( weqlinvrinv ( @op ( abgrfraccarrier X ) ) ( commax ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) isl ) ) .   Defined . 


Opaque abgrfracisinv . 

Definition abgrfrac ( X : abmonoid ) : abgr := abgrconstr ( abgrfraccarrier X ) ( abgrfracinv X ) ( abgrfracisinv X ) .  

Definition prabgrfrac ( X : abmonoid ) : X -> X -> abgrfrac X := fun x x' : X => setquotpr ( eqrelabgrfrac X ) ( dirprodpair x x' ) .

(** **** Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrfrac ( X : abmonoid ) : weq ( abmonoidfrac X ( totalsubmonoid X ) ) ( abgrfrac X ) .
Proof . intros . apply ( weqsetquotweq ( eqrelabmonoidfrac  X ( totalsubmonoid X ) ) ( eqrelabgrfrac X ) ( weqdirprodf ( idweq X ) ( weqtotalsubtype X ) ) ) .    simpl .  intros x x' .  destruct x as [ x1 x2 ] . destruct x' as [ x1' x2' ] . simpl in * . apply hinhfun . intro tt0 . destruct tt0 as [ xx0 is0 ] .   split with ( pr21 xx0 ) .  apply is0 . 
simpl .  intros x x' .  destruct x as [ x1 x2 ] . destruct x' as [ x1' x2' ] . simpl in * . apply hinhfun . intro tt0 . destruct tt0 as [ xx0 is0 ] .   split with ( carrierpair ( fun x : X => htrue ) xx0 tt  ) .  apply is0 . Defined . 



(** **** Abelian group of fractions in the case when all elements are cancellable *) 


Lemma isinclprabgrfrac ( X : abmonoid ) ( iscanc : forall x : X , isrcancellable ( @op X ) x ) : forall x' : X , isincl ( fun x => prabgrfrac X x x' ) .
Proof . intros . set ( int := isinclprabmonoidfrac X ( totalsubmonoid X ) ( fun a : totalsubmonoid X => iscanc ( pr21 a ) ) ( carrierpair ( fun x : X => htrue ) x' tt ) ) . 
set ( int1 := isinclcomp ( inclpair _ int ) ( weqabgrfrac X ) ) . apply int1 .  Defined . 

Lemma isdeceqabgrfrac ( X : abmonoid ) ( iscanc : forall x : X , isrcancellable ( @op X ) x ) ( is : isdeceq X ) : isdeceq ( abgrfrac X ) .
Proof . intros . apply ( isdeceqweqf ( weqabgrfrac X ) ) .   apply ( isdeceqabmonoidfrac X ( totalsubmonoid X ) ( fun a : totalsubmonoid X => iscanc ( pr21 a ) ) is ) . Defined .  




Close Scope addoperation_scope . 


(** *** Rings *)


(** **** General definitions *)

Definition isrng ( X : setwith2binop ) := isrngops ( @op1 X ) ( @op2 X ) .

Definition rng := total2 ( fun X : setwith2binop =>  isrng X )  .
Definition rngpair { X : setwith2binop } ( is : isrng X ) : rng  := tpair ( fun X : setwith2binop =>  isrng X ) X is .
Definition pr21rng : rng -> setwith2binop := @pr21 _ ( fun X : setwith2binop =>  isrng X ) .
Coercion pr21rng : rng >-> setwith2binop . 

Definition rngaxs ( X : rng ) : isrngops ( @op1 X ) ( @op2 X ) := pr22 X . 

Definition rngop1axs ( X : rng ) : isabgroupop ( @op1 X ) := pr21 ( pr21 ( pr22 X ) ) .
Definition rngassoc1 ( X : rng ) : isassoc ( @op1 X ) := assocax_is ( rngop1axs X ) . 
Definition rngunel1 { X : rng } : X := unel_is ( rngop1axs X ) . 
Definition rnglunax1 ( X : rng ) : islunit op1 ( @rngunel1 X ) := lunax_is ( rngop1axs X ) .
Definition rngrunax1 ( X : rng ) : isrunit op1 ( @rngunel1 X ) := runax_is ( rngop1axs X ) .
Definition rnginv1 ( X : rng ) : X -> X := grinv_is ( rngop1axs X ) .
Definition rnglinvax1 ( X : rng ) : forall x : X , paths ( op1 ( rnginv1 X x ) x ) rngunel1 := grlinvax_is ( rngop1axs X ) .
Definition rngrinvax1 ( X : rng ) : forall x : X , paths ( op1 x ( rnginv1 X x ) ) rngunel1 := grrinvax_is ( rngop1axs X ) . 
Definition rngcomm1 ( X : rng ) : iscomm ( @op1 X ) := commax_is ( rngop1axs X ) .
 

Definition rngop2axs ( X : rng ) : ismonoidop ( @op2 X ) := pr22 ( pr21 ( pr22 X ) ) .
Definition rngassoc2 ( X : rng ) : isassoc ( @op2 X ) := assocax_is ( rngop2axs X ) . 
Definition rngunel2 { X : rng } : X := unel_is ( rngop2axs X ) . 
Definition rnglunax2 ( X : rng ) : islunit op2 ( @rngunel2 X ) := lunax_is ( rngop2axs X ) .
Definition rngrunax2 ( X : rng ) : isrunit op2 ( @rngunel2 X ) := runax_is ( rngop2axs X ) .


Definition rngdistraxs ( X : rng ) : isdistr ( @op1 X ) ( @op2 X ) := pr22 ( pr22 X ) .
Definition rngldistrax ( X : rng ) : isldistr ( @op1 X ) ( @op2 X ) := pr21 ( pr22 ( pr22 X ) ) .
Definition rngrdistrax ( X : rng ) : isrdistr ( @op1 X ) ( @op2 X ) := pr22 ( pr22 ( pr22 X ) ) .  

Definition rngconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : isgroupop opp1 ) ( ax12 : iscomm opp1 ) ( ax2 : ismonoidop opp2 ) ( dax : isdistr opp1 opp2 ) : rng := @rngpair ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) ( dirprodpair ( dirprodpair ( dirprodpair ax11 ax12 ) ax2 ) dax ) .   

Definition rngmultx0 ( X : rng ) : forall x : X , paths ( op2 x rngunel1 ) rngunel1 := rngmultx0_is ( rngaxs X ) .  
Definition rngmult0x ( X : rng ) : forall x : X , paths ( op2 rngunel1 x ) rngunel1 := rngmult0x_is ( rngaxs X ) .
Definition rngminus1 { X : rng } : X := rngminus1_is ( rngaxs X ) . 
Definition rngmultwithminus1 ( X : rng ) : forall x : X , paths ( op2 rngminus1 x ) ( rnginv1 X x ) := rngmultwithminus1_is ( rngaxs X ) .
  

Definition addabgr ( X : rng ) : abgr := abgrpair ( setwithbinoppair X op1 ) ( rngop1axs X ) .
Definition multmonoid ( X : rng ) : monoid := monoidpair  ( setwithbinoppair X op2 ) ( rngop2axs X ) .

Notation "x + y" := ( op1 x y ) : rng_scope .
Notation "x * y" := ( op2 x y ) : rng_scope . 
Notation "0" := ( rngunel1 ) : rng_scope .   
Notation "1" := ( rngunel2 ) : rng_scope .
Notation "-1" := ( rngminus1 ) ( at level 0 ) : rng_scope . 



(** **** Subobjects *)

Definition issubrng { X : rng } ( A : hsubtypes X ) := dirprod ( @issubgr ( addabgr X ) A ) ( @issubmonoid ( multmonoid X ) A ) . 

Lemma isapropissubrng { X : rng } ( A : hsubtypes X ) : isaprop ( issubrng A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubgr . apply isapropissubmonoid . Defined . 

Definition subrngs ( X : rng ) := total2 ( fun  A : hsubtypes X => issubrng A ) .
Definition subrngpair { X : rng } := tpair ( fun  A : hsubtypes X => issubrng A ) .
Definition pr21subrng ( X : rng ) : @subrngs X -> hsubtypes X := @pr21 _ (fun  A : hsubtypes X => issubrng A ) .

Definition subrngtosubsetswith2binop ( X : rng ) : subrngs X -> @subsetswith2binop X := fun A : _ => subsetswith2binoppair ( pr21 A ) ( dirprodpair ( pr21 ( pr21 ( pr21 ( pr22 A ) ) ) ) ( pr21 ( pr22 ( pr22 A ) ) ) ) . 
Coercion subrngtosubsetswith2binop : subrngs >-> subsetswith2binop . 

Definition addsubgr { X : rng } : subrngs X -> @subgrs ( addabgr X ) := fun A : _ => @subgrpair ( addabgr X ) ( pr21 A ) ( pr21 ( pr22 A ) ) .
Definition multsubmonoid { X : rng } : subrngs X -> @submonoids ( multmonoid X ) := fun A : _ => @submonoidpair ( multmonoid X ) ( pr21 A ) ( pr22 ( pr22 A ) ) .  

Lemma isrngcarrier { X : rng } ( A : subrngs X ) : isrng A .
Proof . intros . split with ( dirprodpair ( isabgrcarrier ( addsubgr A ) ) ( ismonoidcarrier ( multsubmonoid A ) ) ) . split .    

intros a b c . apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply rngldistrax .  
intros a b c . apply ( invmaponpathsincl _ ( isinclpr21carrier A ) ) .  simpl . apply rngrdistrax . Defined .   

Definition carrierofasubrng ( X : rng ) ( A : subrngs X ) : rng .
Proof . intros . split with A . apply isrngcarrier .  Defined . 

Coercion carrierofasubrng : subrngs >-> rng .  


(** **** Quotient objects *)

Definition rngeqrel { X : rng } := @twobinopeqrel X .
Identity Coercion id_rngeqrel : rngeqrel >-> twobinopeqrel .

Definition addabgreqrel { X : rng } ( R : @rngeqrel X ) : @binopeqrel ( addabgr X ) := @binopeqrelpair ( addabgr X ) ( pr21 R ) ( pr21 ( pr22 R ) ) .     

Definition multmonoideqrel { X : rng } ( R : @rngeqrel X ) : @binopeqrel ( multmonoid X ) := @binopeqrelpair ( multmonoid X ) ( pr21 R ) ( pr22 ( pr22 R ) ) .

Lemma isrngquot { X : rng } ( R : @rngeqrel X ) : isrng ( setwith2binopquot R ) . 
Proof . intros . split with ( dirprodpair ( isabgrquot ( addabgreqrel R ) ) ( ismonoidquot ( multmonoideqrel R ) ) ) .  simpl . set ( opp1 := @op1 ( setwith2binopquot R ) ) . set ( opp2 := @op2 ( setwith2binopquot R ) ) .  split .   

unfold isldistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  x'' ( opp1 x x' ) ) ( opp1 ( opp2 x'' x ) ( opp2 x'' x' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rngldistrax X x x' x'' ) ) .  

unfold isrdistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  ( opp1 x x' ) x''  ) ( opp1 ( opp2 x x'' ) ( opp2 x' x'' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rngrdistrax X x x' x'' ) ) .  Defined .

Definition rngquot { X : rng } ( R : @rngeqrel X ) : rng := @rngpair ( setwith2binopquot R ) ( isrngquot R ) .   



(** **** Direct products *)

Lemma isrngdirprod ( X Y : rng ) : isrng ( setwith2binopdirprod X Y ) .
Proof . intros . split with ( dirprodpair ( isabgrdirprod ( addabgr X ) ( addabgr Y ) ) ( ismonoiddirprod ( multmonoid X ) ( multmonoid Y ) ) ) . simpl .  split . 

intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rngldistrax X ) .  apply ( rngldistrax Y ) . 
intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rngrdistrax X ) .  apply ( rngrdistrax Y ) .  Defined . 


Definition rngdirprod ( X Y : rng ) := @rngpair ( setwith2binopdirprod X Y ) ( isrngdirprod X Y ) . 



(** *** Commutative rings *)

(** **** General definitions *)

Definition iscommrng ( X : setwith2binop ) := iscommrngops ( @op1 X ) ( @op2 X ) .

Definition commrng := total2 ( fun X : setwith2binop => iscommrng X ) .
Definition commrngpair := tpair ( fun X : setwith2binop => iscommrng X ) .

Definition commrngconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : isgroupop opp1 ) ( ax12 : iscomm opp1 ) ( ax21 : ismonoidop opp2 ) ( ax22 : iscomm opp2 ) ( dax : isdistr opp1 opp2 ) : commrng := @commrngpair ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) ( dirprodpair ( dirprodpair ( dirprodpair ( dirprodpair ax11 ax12 ) ax21 ) dax ) ax22 ) . 

Definition commrngtorng : commrng -> rng := fun X : _ => @rngpair ( pr21 X ) ( pr21 ( pr22 X ) ) . 
Coercion commrngtorng : commrng >-> rng .

Definition rngcomm2 ( X : commrng ) : iscomm ( @op2 X ) := pr22 ( pr22 X ) . 
Definition commrngop2axs ( X : commrng ) : isabmonoidop ( @op2 X ) := tpair _ ( rngop2axs X ) ( rngcomm2 X ) . 


Definition multabmonoid ( X : commrng ) : abmonoid := abmonoidpair ( setwithbinoppair X op2 ) ( dirprodpair ( rngop2axs X ) ( rngcomm2 X ) ) . 


(** **** Subobjects *)

Lemma iscommrngcarrier { X : commrng } ( A : @subrngs X ) : iscommrng A .
Proof . intros . split with ( isrngcarrier A ) . apply ( pr22 ( @isabmonoidcarrier ( multabmonoid X ) ( multsubmonoid A ) ) ) .  Defined . 

Definition carrierofasubcommrng { X : commrng } ( A : @subrngs X ) : commrng := commrngpair A ( iscommrngcarrier A ) . 


(** **** Quotient objects *)

Lemma iscommrngquot { X : commrng } ( R : @rngeqrel X ) : iscommrng ( setwith2binopquot R ) . 
Proof . intros . split with ( isrngquot R ) . apply ( pr22 ( @isabmonoidquot  ( multabmonoid X ) ( multmonoideqrel R ) ) ) .  Defined . 

Definition commrngquot { X : commrng } ( R : @rngeqrel X ) := commrngpair ( setwith2binopquot R ) ( iscommrngquot R ) . 




(** **** Direct products *)

Lemma iscommrngdirprod ( X Y : commrng ) : iscommrng ( setwith2binopdirprod X Y ) .
Proof . intros . split with ( isrngdirprod X Y ) . apply ( pr22 ( isabmonoiddirprod ( multabmonoid X ) ( multabmonoid Y ) ) ) . Defined . 

Definition commrngdirprod ( X Y : commrng ) := commrngpair ( setwith2binopdirprod X Y ) ( iscommrngdirprod X Y ) . 


   

(** **** Rings of fractions *)

Open Scope rng_scope . 

Definition commrngfracop1int (  X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : binop ( dirprod X S ) := fun x1s1 x2s2 : dirprod X S =>  @dirprodpair X S ( ( ( pr21 ( pr22 x2s2 ) ) * ( pr21 x1s1 ) ) + ( ( pr21 ( pr22 x1s1 ) ) * ( pr21 x2s2 ) ) ) ( @op S ( pr22 x1s1 ) ( pr22 x2s2 ) )  .

Definition commrngfracop2int (  X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : binop ( dirprod X S ) := abmonoidfracopint ( multabmonoid X ) S . 

Definition commrngfracunel1int ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : dirprod X S := dirprodpair 0 ( unel S ) .

Definition commrngfracunel2int ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : dirprod X S := dirprodpair 1 ( unel S ) . 

Definition commrngfracinv1int  ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : dirprod X S -> dirprod X S := fun xs : _ => dirprodpair ( ( -1 ) * ( pr21 xs ) ) ( pr22 xs ) .

Definition eqrelcommrngfrac (  X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : eqrel ( dirprod X S ) := eqrelabmonoidfrac ( multabmonoid X ) S . 

Lemma commrngfracl1 ( X : commrng ) ( x1 x2 x3 x4 a1 a2 s1 s2 s3 s4 : X ) ( eq1 : paths ( ( x1 * s2 ) * a1 ) ( ( x2 * s1 ) * a1 ) ) ( eq2 : paths ( ( x3 * s4 ) * a2 ) ( ( x4 * s3 ) * a2 ) ) : paths ( ( ( ( s3 * x1 ) + ( s1 * x3 ) ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( ( s4 * x2 ) + ( s2 * x4 ) ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) .
Proof . intros . set ( rdistr := rngrdistrax X ) . set ( assoc2 := rngassoc2 X ) . set ( op2axs := commrngop2axs X ) . set ( comm2 := rngcomm2 X ) . set ( rer := abmonoidoprer op2axs ) . 

rewrite ( rdistr ( s3 * x1 ) ( s1 * x3 )  ( s2 * s4 ) ) . rewrite ( rdistr ( s4 * x2 ) ( s2 * x4 ) ( s1 * s3 ) ) .  rewrite ( rdistr ( ( s3 * x1 ) * ( s2 * s4 ) ) ( ( s1 * x3 ) * ( s2 * s4 ) )  ( a1 * a2 ) ) . rewrite ( rdistr ( ( s4 * x2 ) * ( s1 * s3 ) ) ( ( s2 * x4 ) * ( s1 * s3 ) ) ( a1 * a2 ) ) .  clear rdistr .  

assert ( e1 : paths ( ( ( s3 * x1 ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( s4 * x2 ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) ) .  destruct ( assoc2 ( s3 * x1 ) s2 s4  ) .  rewrite ( assoc2 s3 x1 s2 ) .  rewrite ( rer ( s3 * ( x1 * s2 ) ) s4 a1 a2 ) .  rewrite ( assoc2 s3 ( x1 * s2 ) a1 ) .  destruct ( assoc2 ( s4 * x2 ) s1 s3  ) .  rewrite ( assoc2 s4 x2 s1 ) .  rewrite ( rer ( s4 * ( x2 * s1 ) ) s3 a1 a2 ) . rewrite ( assoc2 s4 ( x2 * s1 ) a1 ) . destruct eq1 .  rewrite ( comm2 s3 ( ( x1 * s2 ) * a1 ) ) . rewrite ( comm2 s4 ( ( x1 * s2 ) * a1 ) ) .  rewrite ( rer ( ( x1 * s2 ) * a1 ) s3 s4 a2 ) .  apply idpath .  

assert ( e2 : paths ( ( ( s1 * x3 ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( s2 * x4 ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) ) .  destruct ( comm2 s4 s2 ) .  destruct ( comm2 s3 s1 ) .  destruct ( comm2 a2 a1 ) . destruct ( assoc2 ( s1 * x3 ) s4 s2 ) .  destruct ( assoc2 ( s2 * x4 ) s3 s1 ) .  rewrite ( assoc2 s1 x3 s4 ) .  rewrite ( assoc2 s2 x4 s3 ) .  rewrite ( rer ( s1 * ( x3 * s4 ) ) s2 a2 a1 ) .  rewrite ( rer ( s2 * ( x4 * s3 ) ) s1 a2 a1 ) .  rewrite ( assoc2 s1 ( x3 * s4 ) a2 ) .  rewrite ( assoc2 s2 ( x4 * s3 ) a2 ) . destruct eq2 . destruct ( comm2 ( ( x3 * s4 ) * a2 ) s1 ) .  destruct ( comm2 ( ( x3 *s4 ) * a2 ) s2 ) . rewrite ( rer ( ( x3 * s4 ) * a2 ) s1 s2 a1 ) . apply idpath .  

destruct e1 . destruct e2 . apply idpath . Defined .  

Opaque commrngfracl1 .  

Lemma commrngfracop1comp ( X : commrng ) ( S :  @subabmonoids ( multabmonoid X ) ) : iscomprelrelfun2 ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S )  ( commrngfracop1int X S ) .
Proof . intros .  intros xs1 xs2 xs3 xs4 .  simpl .  set ( ff := @hinhfun2 ) .  simpl in ff . apply ff . clear ff . intros tt1 tt2 . split with ( @op S ( pr21 tt1 ) ( pr21 tt2 ) ) .  assert ( eq1 := pr22 tt1 ) .  simpl in eq1 .  assert ( eq2 := pr22 tt2 ) . simpl in eq2 . unfold pr21carrier . 
apply ( commrngfracl1 X ( pr21 xs1 ) ( pr21 xs2 ) ( pr21 xs3 ) ( pr21 xs4 ) ( pr21 ( pr21 tt1 ) ) ( pr21 ( pr21 tt2 ) ) ( pr21 ( pr22 xs1 ) )  ( pr21 ( pr22 xs2 ) ) ( pr21 ( pr22 xs3 ) ) ( pr21 ( pr22 xs4 ) ) eq1 eq2 ) . Defined . 

Opaque commrngfracop1comp .

Definition commrngfracop1 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : binop ( setquotinset ( eqrelcommrngfrac X S ) ) := setquotfun2 ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracop1int X S ) ( commrngfracop1comp X S ) .

Lemma commrngfracl2 ( X : commrng ) ( x x' x'' s s' s'' : X ) : paths ( ( s'' * ( ( s' * x ) + ( s * x' ) ) ) + ( ( s * s' ) * x'' ) ) ( ( ( s' * s'' ) * x ) + ( s * ( ( s'' * x' ) + ( s' * x'' ) ) ) ) .
Proof. intros . set ( ldistr := rngldistrax X ) . set ( comm2 := rngcomm2 X ) . set ( assoc2 := rngassoc2 X ) . set ( assoc1 := rngassoc1 X ) . rewrite ( ldistr ( s' * x ) ( s * x' ) s'' ) .  rewrite ( ldistr ( s'' * x' ) ( s' * x'' ) s ) .  destruct ( comm2 s'' s' ) .  destruct ( assoc2 s'' s' x ) . destruct ( assoc2 s'' s x' ) .  destruct ( assoc2 s s'' x' ) .  destruct ( comm2 s s'' ) .  destruct ( assoc2 s s' x'' ) . apply ( assoc1 ( ( s'' * s' ) * x ) ( ( s * s'' ) * x' ) ( ( s * s' ) * x'' ) ) .  Defined .

Opaque commrngfracl2 .


Lemma commrngfracl3 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : isassoc ( commrngfracop1 X S ) .
Proof . intros . set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) .  unfold isassoc . 
assert ( int : forall xs xs' xs'' : dirprod X S , paths ( setquotpr R ( add1int ( add1int xs xs' ) xs'' ) ) ( setquotpr R ( add1int xs ( add1int xs' xs'' ) ) ) ) . unfold add1int . unfold commrngfracop1int . intros xs xs' xs'' .  apply ( @maponpaths _ _ ( setquotpr R ) ) .   simpl .  apply pathsdirprod . unfold pr21carrier . apply ( commrngfracl2 X  ( pr21 xs ) ( pr21 xs' ) ( pr21 xs'' ) ( pr21 ( pr22 xs ) )  ( pr21 ( pr22 xs' ) ) ( pr21 ( pr22 xs'' ) ) ) . apply ( invmaponpathsincl _ ( isinclpr21carrier ( pr21 S ) ) ) .  unfold pr21carrier . simpl .  set ( assoc2 := rngassoc2 X ) .  apply ( assoc2 (pr21 (pr22 xs)) (pr21 (pr22 xs')) (pr21 (pr22 xs'')) ) . 

apply ( setquotuniv3prop R ( fun x x' x'' : setquotinset R => @eqset ( setquotinset R ) ( add1 ( add1 x x' ) x'') ( add1 x ( add1 x' x'') ) ) int ) . Defined .   
  
Opaque commrngfracl3 .

Lemma commrngfracl5 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : iscomm ( commrngfracop1 X S ) .
Proof . intros .  set ( R := eqrelcommrngfrac X S ) .  set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . unfold iscomm . apply ( setquotuniv2prop R ( fun x x' : setquotinset R  => @eqset ( setquotinset R ) ( add1 x x') ( add1 x' x ) ) ) . intros xs xs' .   apply ( @maponpaths _ _ ( setquotpr R ) ( add1int xs xs' ) ( add1int xs' xs ) ) .  unfold add1int . unfold commrngfracop1int . destruct xs as [ x s ] . destruct s as [ s iss ] . destruct xs' as [ x' s' ] . destruct s' as [ s' iss' ] . simpl .   apply pathsdirprod .  

change ( paths ( ( s' * x) + ( s * x' ) ) ( ( s * x' ) + ( s' * x ) ) ) . destruct ( rngcomm1 X ( s' * x ) ( s * x' ) ) . apply idpath . 

apply ( invmaponpathsincl _ ( isinclpr21carrier ( pr21 S ) ) ) .  simpl .  change (  paths ( s * s' ) ( s' * s ) ) . apply ( rngcomm2 X ) . Defined . 

Opaque commrngfracl5 .


Definition commrngfracunel1 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) := setquotpr  ( eqrelcommrngfrac X S ) ( commrngfracunel1int X S ) .

Definition commrngfracunel2 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) := setquotpr  ( eqrelcommrngfrac X S ) ( commrngfracunel2int X S ) . 

Lemma commrngfracinv1comp ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : iscomprelrelfun ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracinv1int X S ) .
Proof . intros . set ( assoc2 := rngassoc2 X ) . intros xs xs' .  simpl .  set ( ff := @hinhfun ) .  simpl in ff . apply ff . clear ff .  intro tt0 .  split with ( pr21 tt0 ) . set ( x := pr21 xs ) . set ( s := pr21 ( pr22 xs ) ) . set ( x' := pr21 xs' ) . set ( s' := pr21 ( pr22 xs' ) ) . set ( a0 := pr21 ( pr21 tt0 ) ) .  change ( paths ( -1 * x * s' * a0 ) ( -1 * x' * s * a0 ) ) . rewrite ( assoc2 -1 x s' ) .  rewrite ( assoc2 -1 x' s ) . rewrite ( assoc2 -1 ( x * s' ) a0 ) . rewrite ( assoc2 -1 ( x' * s ) a0 ) . apply ( maponpaths ( fun x0 : X => -1 * x0 ) ( pr22 tt0 ) ) . Defined .   

Definition commrngfracinv1 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) := setquotfun ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracinv1int X S ) ( commrngfracinv1comp X S ) . 

Lemma commrngfracisinv1 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : isinv ( commrngfracop1 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) .
Proof . intros .  

assert ( isl : islinv  ( commrngfracop1 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) ) . set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . set ( inv1 := commrngfracinv1 X S ) . set ( inv1int := commrngfracinv1int X S ) . set ( qunel1int := commrngfracunel1int X S ) .  set ( qunel1 := commrngfracunel1 X S) . set ( assoc2 := rngassoc2 X ) .  unfold islinv . apply ( setquotunivprop R ( fun  x : setquotinset R => @eqset ( setquotinset R ) ( add1 ( inv1 x ) x ) qunel1 ) ) .  intro xs .   apply ( iscompsetquotpr R  ( add1int ( inv1int xs ) xs ) qunel1int ) . simpl . apply hinhpr .  split with ( unel S ) .  set ( x := pr21 xs ) . set ( s := pr21 ( pr22 xs ) ) . change ( paths ( ( s * ( -1 * x ) + s * x ) * 1 * 1 ) ( 0 * ( s * s ) * 1 ) ) .  destruct ( rngldistrax X ( -1 * x ) x s ) . rewrite ( rngmultwithminus1 X x ) . rewrite ( rnglinvax1 X x ) .  rewrite ( rngmultx0 X s ) . rewrite ( rngmult0x X 1 ) .  rewrite ( rngmult0x X 1 ) . rewrite ( rngmult0x X ( s * s ) ) . apply ( pathsinv0 ( rngmult0x X 1 ) ) .

apply ( dirprodpair isl ( weqlinvrinv ( commrngfracop1 X S ) ( commrngfracl5 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) isl ) ) .  Defined .  

Opaque commrngfracisinv1 . 


Lemma commrngfracl4l ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : islunit ( commrngfracop1 X S ) ( commrngfracunel1 X S ) .
Proof . intros .  set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . set ( un1 := commrngfracunel1 X S ). 
unfold islunit .  apply ( setquotunivprop R ( fun x : _ => @eqset ( setquotinset R ) (add1 un1 x) x ) ) .  intro xs . 
assert ( e0 : paths ( add1int ( commrngfracunel1int X S ) xs ) xs ) .  unfold add1int . unfold commrngfracop1int .  destruct xs as [ x s ] . destruct s as [ s iss ] .  apply pathsdirprod . simpl .    change ( paths ( ( s * 0 ) + ( 1 * x ) ) x ) . rewrite (  @rngmultx0 X s  ) . rewrite ( rnglunax2 X x ) . rewrite ( rnglunax1 X x ) . apply idpath . apply ( invmaponpathsincl _ ( isinclpr21carrier ( pr21 S ) ) ) . change ( paths ( 1 * s ) s ) .  apply ( rnglunax2 X s ) .  apply ( maponpaths ( setquotpr R ) e0 ) . Defined .

Opaque commrngfracl4l .

Lemma commrngfracl4r ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : isrunit ( commrngfracop1 X S ) ( commrngfracunel1 X S ) .
Proof . intros . apply ( weqlunitrunit (commrngfracop1 X S) ( commrngfracl5 X S ) (commrngfracunel1 X S) ( commrngfracl4l X S ) ) .  Defined .  

Opaque commrngfracl4r .

Definition commrngfracl4 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : ismonoidop ( commrngfracop1 X S ) := tpair _ ( commrngfracl3 X S ) ( tpair _ ( commrngfracunel1 X S ) ( dirprodpair ( commrngfracl4l X S ) ( commrngfracl4r X S ) ) ) . 


Definition commrngfracop2 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : binop ( setquotinset ( eqrelcommrngfrac X S ) ) := abmonoidfracop ( multabmonoid X ) S .

Lemma commrngfracl6 ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : iscomm ( commrngfracop2 X S ) .
Proof . intros . apply ( commax ( abmonoidfrac ( multabmonoid X ) S ) ) . Defined .   

Opaque commrngfracl6 .


Lemma commrngfracl7l  ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : isldistr ( commrngfracop1 X S ) ( commrngfracop2 X S ) .
Proof . intros . set ( R := eqrelcommrngfrac X S ) . set ( mult1int := commrngfracop2int X S ) . set ( mult1 := commrngfracop2 X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) .  unfold isldistr .  apply ( setquotuniv3prop R ( fun x x' x'' : setquotinset R  => @eqset ( setquotinset R ) ( mult1 x'' ( add1 x x')) ( add1 ( mult1 x'' x) ( mult1  x'' x')) ) ) . intros xs xs' xs'' .  apply ( iscompsetquotpr R ( mult1int xs'' ( add1int xs xs' ) ) ( add1int ( mult1int xs'' xs ) ( mult1int xs'' xs' ) ) ) . 

destruct xs as [ x s ] .  destruct xs' as [ x' s' ] . destruct xs'' as [ x'' s'' ] . destruct s'' as [ s'' iss'' ] . simpl . apply hinhpr . split with ( unel S ) . 
destruct s as [ s iss ] .  destruct s' as [ s' iss' ] . simpl . 

change ( paths ( ( ( x'' * ( ( s' * x ) + ( s * x' ) ) ) * ( ( s'' * s ) * ( s'' * s' ) ) ) * 1 ) ( ( ( ( ( s'' * s') * ( x'' * x ) ) + ( ( s'' * s ) * ( x'' * x' ) ) ) * ( s'' * ( s * s' ) ) ) * 1 ) ) . 

rewrite ( rngldistrax X ( s' * x ) ( s * x' ) x'' ) .  rewrite ( rngrdistrax X _ _ ( ( s'' * s) * ( s'' * s') ) ) .  rewrite ( rngrdistrax X _ _ ( s'' * ( s * s') ) ) .  set ( assoc := rngassoc2 X ) . set ( comm := rngcomm2 X ) . set ( rer := @abmonoidoprer X ( @op2 X ) ( commrngop2axs X ) ) . 

assert ( e1 : paths ( ( x'' * ( s' * x ) ) * ( ( s'' * s ) * ( s'' * s' ) ) ) ( ( ( s'' * s') * ( x'' * x ) ) * ( s'' * ( s * s' ) ) ) ) . destruct ( assoc x'' s' x ) .  destruct ( comm s' x'' ) .  rewrite ( assoc s' x'' x ) .  destruct ( comm (  x'' * x ) s' ) .  destruct ( comm (  x'' * x ) (  s'' * s' ) ) .  destruct ( assoc s'' s s' ) . destruct ( comm (  s'' * s' ) (  s'' * s ) ) .  destruct ( comm s' (  s'' * s ) ) . destruct ( rer (  x'' * x ) s' (  s'' * s' ) (  s'' * s ) ) .  apply idpath . 

assert ( e2 : paths ( ( x'' * ( s * x' ) ) * ( ( s'' * s ) * ( s'' * s' ) ) )  ( ( ( s'' * s ) * ( x'' * x' ) ) * ( s'' * ( s * s' ) ) ) ) . destruct ( assoc x'' s x' ) .  destruct ( comm s x'' ) .  rewrite ( assoc s x'' x' ) .  destruct ( comm (  x'' * x' ) s ) .  destruct ( comm (  x'' * x' ) (  s'' * s ) ) . destruct ( rer (  x'' * x' ) (  s'' * s ) s (  s'' * s' ) ) .  destruct ( assoc s s'' s' ) . destruct ( assoc s'' s s' ) . destruct ( comm s s'' ) . apply idpath .

rewrite e1 .  rewrite e2 . apply idpath . Defined .  

Opaque commrngfracl7l .


Lemma commrngfracl7r  ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : isrdistr ( commrngfracop1 X S ) ( commrngfracop2 X S ) .
Proof . intros . apply ( weqldistrrdistr (commrngfracop1 X S) ( commrngfracop2 X S ) ( commrngfracl6 X S ) ( commrngfracl7l X S ) ) .  Defined .  


  

(** Notes : 

1. Construction of the addition on the multiplicative monoid of fractions requires only commutativity and associativity of multiplication and ( right ) distributivity . No properties of the addition are used . 

2. The proof of associtivity for the addition on the multiplicative monoid of fractions requires in the associativity of the original addition but no other properties . 

*) 

Definition commrngfrac ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : commrng .   
Proof .  intros .  set ( R := eqrelcommrngfrac  X S ) . set ( mult1 := commrngfracop2 X S ) . set ( add1 := commrngfracop1 X S ) . set ( uset := setquotinset R ) . apply ( commrngconstr add1 mult1 ) . 
split with ( commrngfracl4 X S ) .  split with ( commrngfracinv1 X S ) .  apply ( commrngfracisinv1 X S ) .  apply ( commrngfracl5 X S ) .  apply ( pr22 ( abmonoidfrac ( multabmonoid X ) S ) ) . apply ( commrngfracl6 X S ) .  apply ( dirprodpair ( commrngfracl7l X S ) ( commrngfracl7r X S ) ) .  Defined . 

Definition prcommrngfrac ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : X -> S -> commrngfrac X S := fun x s => setquotpr _ ( dirprodpair x s ) .

Lemma invertibilityincommrngfrac  ( X : commrng ) ( S : @subabmonoids ( multabmonoid X ) ) : forall a a' : S , isinvertible ( @op2 ( commrngfrac X S ) ) ( prcommrngfrac X S ( pr21 a ) a' ) .  
Proof . intros . apply ( invertibilityinabmonoidfrac ( multabmonoid X ) S ) . Defined .  



  

(** **** Ring of fractions in the case when all elements which are being inverted are cancellable *) 

Definition  hrelcommrngfrac0 ( X : commrng ) ( S : @submonoids ( multabmonoid X ) ) : hrel ( dirprod X S ) :=  fun xa yb : setdirprod X S => eqset ( ( pr21 xa ) * ( pr21 ( pr22 yb ) ) )  ( ( pr21 yb ) * ( pr21 ( pr22 xa ) ) ) .

Lemma weqhrelhrel0commrngfrac ( X : commrng ) ( S : @submonoids ( multabmonoid X ) ) ( iscanc : forall a : S , isrcancellable ( @op2 X ) ( pr21carrier _ a ) ) ( xa xa' : dirprod X S ) : weq ( eqrelcommrngfrac X S xa xa' ) ( hrelcommrngfrac0 X S xa xa' ) .
Proof . intros .  unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl .  apply weqimplimpl .  

apply ( @hinhuniv _ ( eqset (pr21 xa * pr21 (pr22 xa')) (pr21 xa' * pr21 (pr22 xa)) ) ) .  intro ae .  destruct ae as [ a eq ] .  apply ( invmaponpathsincl _ ( iscanc a ) _ _ eq ) . 
intro eq . apply hinhpr . split with ( unel S ) . rewrite ( rngrunax2 X )  .  rewrite ( rngrunax2 X ) .  apply eq . apply ( isapropishinh _ ) .  apply ( setproperty X ) .   Defined .

Opaque weqhrelhrel0abmonoidfrac .


Lemma isinclprcommrngfrac ( X : commrng ) ( S : @submonoids ( multabmonoid X ) ) ( iscanc : forall a : S , isrcancellable ( @op2 X ) ( pr21carrier _ a ) ) : forall a' : S , isincl ( fun x => prcommrngfrac X S x a' ) .
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) .  apply ( setproperty ( commrngfrac X S ) ) .  intros x x' .   intro e .  set ( e' := invweq ( weqpathsinsetquot ( eqrelcommrngfrac X S ) ( dirprodpair x a' ) ( dirprodpair x' a' ) )  e ) . set ( e'' := weqhrelhrel0commrngfrac X S iscanc ( dirprodpair _ _ ) ( dirprodpair _ _ ) e' )  . simpl in e'' . apply ( invmaponpathsincl _ ( iscanc a' ) ) . apply e'' .  Defined . 


Lemma isdeceqcommrngfrac ( X : commrng ) ( S : @submonoids ( multabmonoid X ) ) ( iscanc : forall a : S , isrcancellable ( @op2 X ) ( pr21carrier _ a ) ) ( is : isdeceq X ) : isdeceq ( commrngfrac X S ) .
Proof . intros . apply ( isdeceqsetquot ( eqrelcommrngfrac X S ) ) .   intros xa xa' .   apply ( isdecpropweqb ( weqhrelhrel0commrngfrac X S iscanc xa xa' ) ) . apply isdecpropif  . unfold isaprop . simpl . set ( int := setproperty X (pr21 xa * pr21 (pr22 xa')) (pr21 xa' * pr21 (pr22 xa))) . simpl in int . apply int . unfold hrelcommrngfrac0 . unfold eqset .   simpl . apply ( is _ _ ) . Defined . 



Close Scope rng_scope . 















(* To be corrected and completed : 

(** ** Algebraic structures with partial orders *)




(** *** Partially ordered commutative ( abelian ) monoids and commutative ( abelian ) unitary monoids *)



Definition poabmonoidstruct ( X : hSet ) := total2 ( fun mstrr : abmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Definition poabmonoidstructpair { X : hSet } := tpair ( fun mstrr : abmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Definition poabmonoidstructconstr { X : hSet } ( mstrr : abmonoidstruct X ) ( rel : po X ) ( ax :  forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) := poabmonoidstructpair mstrr ( tpair ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) rel ax ) .
Definition pr21poabmonoidstruct ( X : hSet ) : poabmonoidstruct X -> abmonoidstruct X := @pr21 _ ( fun mstrr : abmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Coercion pr21poabmonoidstruct : poabmonoidstruct >-> abmonoidstruct .

Definition poabmonpo { X : hSet } ( mstrr : poabmonoidstruct X ) := pr21 ( pr22 mstrr ) .
Definition poabmonax { X : hSet } ( mstrr : poabmonoidstruct X ) := pr22 ( pr22 mstrr ) . 

Definition poabmonoid := total2 ( fun X : hSet => poabmonoidstruct X ) .
Definition poabmonoidpair := tpair ( fun X : hSet => poabmonoidstruct X ) .
Definition poabmonoidconstr := poabmonoidpair .
Definition pr21poabmonoid : poabmonoid -> hSet := @pr21 _ ( fun X : hSet => poabmonoidstruct X ) .
Coercion pr21poabmonoid : poabmonoid >-> hSet .

Definition poabmonoidtoabmonoid : poabmonoid -> abmonoid := fun X : _ => abmonoidpair ( pr21 X ) ( pr22 X ) . 
Coercion poabmonoidtoabmonoid : poabmonoid >-> abmonoid .

Definition poabmstr { X : poabmonoid } : poabmonoidstruct X := pr22 X . 






Definition pouabmonoidstruct ( X : hSet ) := total2 ( fun mstrr : uabmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Definition pouabmonoidstructpair { X : hSet } := tpair ( fun mstrr : uabmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Definition pouabmonoidstructconstr { X : hSet } ( mstrr : uabmonoidstruct X ) ( rel : po X ) ( ax :  forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) := pouabmonoidstructpair mstrr ( tpair ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) rel ax ) .
Definition pr21pouabmonoidstruct ( X : hSet ) : pouabmonoidstruct X -> uabmonoidstruct X := @pr21 _ ( fun mstrr : uabmonoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstrr x x'' ) ( mstrr x' x'' ) ) ) .
Coercion pr21pouabmonoidstruct : pouabmonoidstruct >-> uabmonoidstruct .

Definition pouabmonoid := total2 ( fun X : hSet => pouabmonoidstruct X ) .
Definition pouabmonoidpair := tpair ( fun X : hSet => pouabmonoidstruct X ) .
Definition pouabmonoidconstr := pouabmonoidpair .
Definition pr21pouabmonoid : pouabmonoid -> hSet := @pr21 _ ( fun X : hSet => pouabmonoidstruct X ) .
Coercion pr21pouabmonoid : pouabmonoid >-> hSet .

Definition pouabmonoidtouabmonoid : pouabmonoid -> uabmonoid := fun X : _ => uabmonoidpair ( pr21 X ) ( pr22 X ) . 
Coercion pouabmonoidtouabmonoid : pouabmonoid >-> uabmonoid .

Definition pouabmstr { X : pouabmonoid } : pouabmonoidstruct X := pr22 X . 






(** **** Partially ordered commutative ( ableian ) groups *)



Definition poabgrstruct ( X : hSet ) := total2 ( fun mstrr : pouabmonoidstruct X => total2 ( fun inv : X -> X => forall x : X , dirprod ( paths ( mstrr ( inv x ) x ) ( unel mstrr ) ) ( paths ( mstrr x ( inv x ) ) ( unel mstrr ) ) ) ) .
Definition poabgrstructpair { X : hSet } := tpair ( fun mstrr : pouabmonoidstruct X => total2 ( fun inv : X -> X => forall x : X , dirprod ( paths ( mstrr ( inv x ) x ) ( unel mstrr ) ) ( paths ( mstrr x ( inv x ) ) ( unel mstrr ) ) ) ) .
Definition poabgrstructconstr { X : hSet } ( mstrr : pouabmonoidstruct X ) ( inv : X -> X ) ( linv : forall x : X , paths ( mstrr ( inv x ) x ) ( unel mstrr ) ) ( rinv : forall x : X , paths ( mstrr x ( inv x ) ) ( unel mstrr ) )  : poabgrstruct X := poabgrstructpair mstrr ( tpair ( fun inv : X -> X => forall x : X , dirprod ( paths ( mstrr ( inv x ) x ) ( unel mstrr ) ) ( paths ( mstrr x ( inv x ) ) ( unel mstrr ) ) ) inv ( fun x : X => dirprodpair ( linv x ) ( rinv x ) ) ) . 
Definition pr21poabgrstruct ( X : hSet ) : poabgrstruct X -> pouabmonoidstruct X := @pr21 _ ( fun mstrr : pouabmonoidstruct X => total2 ( fun inv : X -> X => forall x : X , dirprod ( paths ( mstrr ( inv x ) x ) ( unel mstrr ) ) ( paths ( mstrr x ( inv x ) ) ( unel mstrr ) ) ) ) . 
Coercion pr21poabgrstruct : poabgrstruct >-> pouab monoidstruct . 


Definition poabgr := total2 ( fun X : hSet => poabgrstruct X ) .
Definition poabgrpair := tpair ( fun X : hSet => poabgrstruct X ) .
Definition poabgrconstr := poabgrpair .
Definition pr21poabgr : poabgr -> hSet := @pr21 _ ( fun X : hSet => poabgrstruct X ) .
Coercion pr21poabgr : poabgr >-> hSet .






(* Is to be corrected for use :

Definition pomonoidstruct ( X : hSet ) := total2 ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Definition pomonoidstructpair { X : hSet } := tpair ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Definition pomonoidconstr { X : hSet } ( mstr : monoidstruct X ) ( rel : po X ) ( ax :  forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) := pomonoidstructpair mstr ( tpair ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) rel ax ) .
Definition pr21pomonoidstruct ( X : hSet ) : pomonoidstruct X -> monoidstruct X := @pr21 _ ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Coercion pr21pomonoidstruct : pomonoidstruct >-> monoidstruct .

Definition pomonoidstruct ( X : hSet ) := total2 ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Definition pomonoidstructpair { X : hSet } := tpair ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Definition pomonoidconstr { X : hSet } ( mstr : monoidstruct X ) ( rel : po X ) ( ax :  forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) := pomonoidstructpair mstr ( tpair ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) rel ax ) .
Definition pr21pomonoidstruct ( X : hSet ) : pomonoidstruct X -> monoidstruct X := @pr21 _ ( fun mstr : monoidstruct X => total2 ( fun rel : po X => forall x x' x'' : X , rel x x' -> rel ( mstr x x'' ) ( mstr x' x'' ) ) ) .
Coercion pr21pomonoidstruct : pomonoidstruct >-> monoidstruct .

Definition pomonoidstructtopomonoidstruct ( X : hSet ) : pomonoidstruct X -> pomonoidstruct X := fun poum : _ => pomonoidstructpair ( pr21 poum ) ( pr22 poum ) . 
Coercion  pomonoidstructtopomonoidstruct : pomonoidstruct >-> pomonoidstruct .

*)


*)



(* End of the file monandgr.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)