(** * Generalities on hProp.  Vladimir Voevodsky . May - Sep. 2011 . 

In this file we introduce the hProp - an analog of Prop defined based on the univalent semantics. We further introduce the hProp version of the "inhabited" construction - i.e. for any [ T ] in [ UU0 ] we construct an object  [ ishinh T ] and a function [ hinhpr : T -> ishinh T ] which plays the role of [ inhabits ] from the Coq standard library.  The semantic meaning of  [ hinhpr ] is that it is universal among functions from [ T ]  to objects of hProp. Proving that [ ishinh  T ] is in [ hProp ] requires a resizing rule which can be written in the putative notation for such rules as follows :

RR1 ( U1 U2 : Univ ) ( X : U1 ) ( is : isaprop X ) |- X : U2 .

Further in the file we introduce the univalence axiom for hProp and a proof of the fact that it is equivalent to a simplier and better known axiom [ uahp ]. We prove that this axiom implies that [ hProp ] satisfies [ isaset ] i.e. it is a type of h-level 2 . This requires another resizing rule :

RR2 ( U1 U2 : Univ ) |- @hProp U1 : U2 . 

Since resizing rules are not currently implemented in Coq the file does not compile without a patch provided by Hugo Herbelin which turns off the universe consistency verification. We do however keep track of universes in our development "by hand" to ensure that when the resizing rules will become available the current proofs will verify correctly. To point out which results require resizing rules in a substantial way we mark the first few of such reults by (** RR1 *) or (** RR2 *) comment . 

One can achieve similar results with a combination of usual axioms which imitate the resizing rules.  However unlike the usual axioms the resizing rules do not affect the computation/normalization abilities of Coq which makes them the prefrred choice in this situation.


*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** Imports *)


Require Export uu0 . 

(** Universe structure *)

Definition UU0 := UU .

(* end of " Preambule " . *)







(** ** The type [ hProp ] of types of h-level 1 *)

 
Definition hProp := total2 ( fun X : UU0 => isaprop X ) .
Definition hProppair:= tpair (fun X : UU0 => isaprop X ) .
Definition hProppr21 := @pr21 _ _ : hProp -> Type .
Coercion hProppr21: hProp >-> Sortclass.



(** The following re-definitions should make proofs easier in the future when the unification algorithms in Coq are improved . At the moment they create more complications than they eliminate ( e.g. try to prove [ isapropishinh ] with [ isaprop ] in [ hProp ] ) so for the time being they are commented out .


(** *** Re-definitions of some of the standard constructions of uu0 which lift these contructions from UU0 to hProp . *)


Definition iscontr ( X : UU0 ) : hProp := hProppair _ ( isapropiscontr X ) . 

Definition isweq { X Y : UU0 } ( f : X -> Y ) : hProp := hProppair _ ( isapropisweq f ) . 

Definition isofhlevel ( n : nat ) ( X : UU0 ) : hProp := hProppair _ ( isapropisofhlevel n X ) .

Definition isaprop ( X : UU0 ) : hProp := hProppair ( isaprop X ) ( isapropisaprop X ) .

Definition isaset ( X : UU0 ) : hProp := hProppair _ ( isapropisaset X ) .

Definition isisolated ( X : UU0 ) ( x : X ) : hProp := hProppair _ ( isapropisisolated X x ) .

Definition isdeceq ( X : UU0 ) : hProp := hProppair _ ( isapropisdeceq X ) .   

*)


(** ** Intuitionistic logic on [ hProp ] *)


(** *** The [ hProp ] version of the "inhabited" construction. *)



Definition ishinh_UU ( X : UU0 ) := forall P: hProp, ( ( X -> P ) -> P ). 

Lemma isapropishinh ( X : UU0 ) : isaprop ( ishinh_UU X ). (** RR1 *)
Proof. intro. apply impred . intro P . apply impred.  intro. apply ( pr22 P ) .  Defined . 

Definition ishinh ( X : UU0 ) : hProp := hProppair ( ishinh_UU X ) ( isapropishinh X ) . 


Definition hinhpr ( X : UU0 ) : X -> ishinh X := fun x : X => fun P : hProp  => fun f : X -> P => f x .

Definition hinhfun { X Y : UU0 } ( f : X -> Y ) : ishinh_UU X -> ishinh_UU Y := fun isx : ishinh X => fun P : _ =>  fun yp : Y -> P => isx P ( fun x : X => yp ( f x ) ) .

Definition hinhuniv { X : UU0 } { P: hProp } ( f : X -> P ) ( wit : ishinh_UU X ) : P :=  wit P f .

(** Note that the previous definitions do not require RR1 in an essential way ( except for the placing of [ ishinh ] in [ hProp UU0 ] - without RR1 it would be placed in [ hProp UU1 ] ) . The first place where RR1 is essentially required is in application of [ hinhuniv ] to a function [ X -> ishinh Y ] *)


Definition hinhand { X Y : UU0 } ( inx1 : ishinh_UU X ) ( iny1 : ishinh_UU Y) : ishinh ( dirprod X Y ) := fun P:_  => ddualand (inx1 P) (iny1 P).

Definition hinhuniv2 { X Y : UU0 } { P : hProp } ( f : X -> Y -> P ) ( isx : ishinh_UU X ) ( isy : ishinh_UU Y ) : P := hinhuniv ( fun xy : dirprod X Y => f ( pr21 xy ) ( pr22 xy ) ) ( hinhand isx isy ) . 

Definition hinhfun2 { X Y Z : UU0 } ( f : X -> Y -> Z ) ( isx : ishinh_UU X ) ( isy : ishinh_UU Y ) : ishinh Z := hinhfun ( fun xy: dirprod X Y => f ( pr21 xy ) ( pr22 xy ) ) ( hinhand isx isy ) .

Definition hinhunivcor1 ( P : hProp ) : ishinh_UU P -> P := hinhuniv ( idfun P ).
Notation hinhprinv := hinhunivcor1 .


 
(** *** [ ishinh ] and [ coprod ] *)


Lemma hinhcoprod ( X Y : UU0 ) ( is : ishinh_UU ( coprod ( ishinh X ) ( ishinh Y ) ) )  : ishinh ( coprod X Y ) .
Proof. intros . unfold ishinh. intro P .  intro CP.  set (CPX := fun x : X => CP ( ii1 x ) ) . set (CPY := fun y : Y => CP (ii2 y) ).  set (is1P := is P).
 assert ( f : coprod ( ishinh X ) ( ishinh Y ) -> P ) .  apply ( sumofmaps ( hinhuniv CPX ) ( hinhuniv CPY ) ).   apply (is1P f ) . Defined. 

 

(** *** Intuitionistic logic on [ hProp ]. *)


Definition htrue : hProp := hProppair unit isapropunit.

Definition hfalse : hProp := hProppair empty isapropempty.

Definition hconj ( P Q : hProp ) : hProp := hProppair ( dirprod P Q ) (isofhleveldirprod ( S O ) _ _ ( pr22 P ) ( pr22 Q ) ). 

Definition hdisj ( P Q : hProp ) : hProp :=  ishinh ( coprod P Q ) . 

Definition hneg (P: hProp) : hProp.
Proof. intro. split with (P -> empty). apply impred. intro. apply isapropempty. Defined.

Definition himpl (P Q : hProp) : hProp.
Proof. intros. split with (P -> Q). apply impred. intro. apply (pr22  Q). Defined. 

Definition hforall { X : UU0 } ( P : X -> hProp ) : hProp.
Proof. intros. split with (forall x:X, P x). apply impred. intro.  apply (pr22 (P t)). Defined.

Definition hexists { X:UU0 } (P: X -> hProp) : hProp  := ishinh (total2 P).

Definition wittohexists { X : UU0 } (P: X -> hProp)(x:X)(is: P x): hexists P := hinhpr (total2 P) (tpair _ x is).


(** *** Proof of the only non-trivial axiom of intuitionistic logic for our constructions. For the full list of axioms see e.g.  http://plato.stanford.edu/entries/logic-intuitionistic/ *)


Lemma hconjtohdisj (P Q R : hProp) :  hconj ( himpl P R ) ( himpl Q R ) -> himpl ( hdisj P Q ) R .
Proof.  intros P Q R X0. 
assert (s1: hdisj P Q -> R) . intro X1.  
assert (s2: coprod P Q -> R ) . intro X2. destruct X2 as [ XP | XQ ].  apply X0. assumption. apply ( pr22 X0 ).  assumption. 
apply ( hinhuniv s2 ). assumption.  unfold himpl. assumption.  Defined.



(** *** The double negation version of [ hinhabited ] ( does not require RR1 ) . *)


Definition isinhdneg ( X : UU0 ) : hProp := hProppair ( dneg X ) ( isapropdneg X ) .

Definition inhdnegpr (X:UU0): X -> isinhdneg X := todneg X.

Definition inhdnegfun { X Y : UU0 } (f:X -> Y): isinhdneg X -> isinhdneg Y := dnegf  f.

Definition inhdneguniv (X: UU0)(P:UU0)(is:isweq  (todneg P)): (X -> P) -> ((isinhdneg X) -> P) := fun xp:_ => fun inx0:_ => (invmap ( weqpair _ is ) (dnegf  xp inx0)).

Definition inhdnegand (X Y:UU0)(inx0: isinhdneg X)(iny0: isinhdneg Y) : isinhdneg (dirprod X Y) := dneganddnegimpldneg  inx0 iny0.

Definition hinhimplinhdneg (X:UU0)(inx1: ishinh X): isinhdneg X := inx1 hfalse.


(** ** Univalence axiom for hProp 

We introduce here the weakest form of the univalence axiom - the univalence axiom for hProp which is equivalent to the second part of the extensionality axiom in Church simple type theory.  This axiom is easily shown to be equivalent to its version with [paths P P'] as a target and to [ weqtopathshProp ] (see below) as well as to the version of [ weqtopathshProp ] with [ paths P P'] as a target. 

The proof of theorem [ univfromtwoaxiomshProp ] is modeled on the proof of [ univfromtwoaxioms ] from univ01.v 


*)


Axiom uahp : forall P P':hProp,  (P -> P') -> (P' -> P) -> @paths hProp P P'.

Definition eqweqmaphProp { P P': hProp }  ( e: @paths hProp P P' ) : weq P P'.
Proof. intros . destruct e . apply idweq.  Defined.

Definition  weqtopathshProp { P P' : hProp } (w: weq P P' ): @paths hProp P P' := uahp P P' w ( invweq w ) .

Definition weqpathsweqhProp { P P' : hProp } (w : weq P P'): paths (eqweqmaphProp (weqtopathshProp w)) w.
Proof. intros. apply proofirrelevance . apply (isapropweqtoprop P P' (pr22 P')). Defined.


Theorem univfromtwoaxiomshProp (P P':hProp): isweq (@eqweqmaphProp P P').
Proof. intros. 

set (P1:= fun XY: dirprod hProp hProp => (match XY with tpair X Y =>  paths X Y end)). set (P2:= fun XY:  dirprod hProp hProp => match XY with  tpair X Y => weq X Y end). set (Z1:=  total2 P1). set (Z2:=  total2 P2). set (f:= ( totalfun _ _ (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => @eqweqmaphProp X Y end))): Z1 -> Z2). set (g:=  ( totalfun _ _ (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => @weqtopathshProp X Y end))): Z2 -> Z1). set (s1:= (fun X Y :hProp => fun w: weq X Y =>  tpair P2 ( dirprodpair X Y) w)). set (efg:= (fun a:_ => match a as a' return (paths (f (g a')) a') with  tpair ( tpair X Y) w => ( maponpaths (s1 X Y) (@weqpathsweqhProp X Y w)) end)). 

set (h:= fun a1:Z1 => (pr21 ( pr21 a1))).
assert (egf0: forall a1:Z1,  paths ( pr21 (g (f a1))) ( pr21 a1)). intro. apply  idpath.  
assert (egf1: forall a1 a1':Z1,  paths ( pr21 a1') ( pr21 a1) -> paths a1' a1). intros ? ? X .  set (X':=  maponpaths ( @pr21 _ _ )  X). 
assert (is:  isweq h). apply ( isweqpr21pr21). apply ( invmaponpathsweq ( weqpair h is ) _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:= gradth _ _ egf efg). 
apply ( isweqtotaltofib P1 P2  (fun XY: dirprod hProp hProp => (match XY with  tpair X Y => @eqweqmaphProp X Y end)) is2 ( dirprodpair P P')). Defined. 

Definition weqeqweqhProp ( P P' : hProp ) := weqpair _ ( univfromtwoaxiomshProp P P' ) .

Corollary isasethProp : isaset hProp.
Proof. unfold isaset.  simpl. intros x x'. apply (isofhlevelweqb (S O) ( weqeqweqhProp x x' ) (isapropweqtoprop x x' (pr22 x'))). Defined.





(* End of the file hProp.v *)




(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)