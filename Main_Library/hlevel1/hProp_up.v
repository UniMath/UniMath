(** * Univalence Axiom for [ hProp ]

This file contains the formulation of the univalence axiom for hProp and a proof of the fact that it is equivalent to a simplier and better known axiom [ uahp ]. We also prove that this axiom implies that [ hProp ] satisfies [ uu1.isaset ] i.e. it is a type of h-level 2 in UU1. In the addendum file which requires the resizing, or at the moment, the Type in Type patch we show that [ hProp ] satisfies [ isaset ].  *)



(** *** Preambule *)

Add Rec LoadPath "../Generalities".


Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp. 



(** *** Univalence axiom for hProp 

We introduce here the weakest form of the univalence axiom - the univalence axiom for hProp which is equivalent to the second part of the extensionality axiom in Church simple type theory. Right now we have to use uu1. constructions in this section. Eventually, as resizing axioms will become available to push hProp into UU0 which will simplify things considerably. This axiom is easily shown to be equivalent to its version with [uu1.paths UU0 P P'] as a target and to [ weqtopathshProp ] (see below) as well as tothe version of [ weqtopathshProp ] with [ uu1.paths UU0 P P'] as a target. 

The proof of theorem [ univfromtwoaxiomshProp ] is modeled on the proof of [ univfromtwoaxioms ] from univ01.v 


*)


Axiom uahp : forall P P':hProp,  (P -> P') -> (P' -> P) -> uu1.paths hProp P P'.


Definition eqweqmaphProp (P P':hProp) : uu1.paths hProp P P' -> uu1.weq P P'.
Proof. intros. destruct  X. apply uu1.idweq.  Defined.

Definition  weqtopathshProp (P P':hProp)(w: uu1.weq P P'): uu1.paths hProp P P' := uahp P P' w (uu1.weqinv _ _ w).

Definition weqpathsweqhProp (P P':hProp)(w: uu1.weq P P'): uu1.paths _ (eqweqmaphProp _ _ (weqtopathshProp _ _ w)) w.
Proof. intros. apply (uu1.proofirrelevance). apply (uu1.isapropweq P P' (uu1.pr22 _ _ P')). Defined.


Theorem univfromtwoaxiomshProp (P P':hProp): uu1.isweq (uu1.paths hProp P P') (uu1.weq P P') (eqweqmaphProp P P').
Proof. intros. set (P1:= fun XY: uu1.dirprod hProp hProp => (match XY with uu1.tpair X Y =>  uu1.paths hProp X Y end)). set (P2:= fun XY:  uu1.dirprod hProp hProp => match XY with  uu1.tpair X Y => uu1.weq X Y end). set (Z1:=  uu1.total2 _ P1). set (Z2:=  uu1.total2 _ P2). set (f:= ( uu1.totalfun _ _ _ (fun XY: uu1.dirprod hProp hProp => (match XY with  uu1.tpair X Y => eqweqmaphProp X Y end))): Z1 -> Z2). set (g:=  ( uu1.totalfun _ _ _ (fun XY: uu1.dirprod hProp hProp => (match XY with  uu1.tpair X Y => weqtopathshProp X Y end))): Z2 -> Z1). set (s1:= (fun X Y :hProp => fun w: uu1.weq X Y =>  uu1.tpair _ P2 ( uu1.dirprodpair _ _ X Y) w)). set (efg:= (fun a:_ => match a as a' return (uu1.paths _ (f (g a')) a') with  uu1.tpair ( uu1.tpair X Y) w => ( uu1.maponpaths _ _ (s1 X Y) _ _ (weqpathsweqhProp X Y w)) end)). 

set (h:= fun a1:Z1 => (uu1.pr21 _ _ ( uu1.pr21 _ _ a1))).
assert (egf0: forall a1:Z1,  uu1.paths ( uu1.dirprod hProp hProp) ( uu1.pr21 _ _ (g (f a1))) ( uu1.pr21 _ _ a1)). intro. apply  uu1.idpath.  
assert (egf1: forall a1 a1':Z1,  uu1.paths _ ( uu1.pr21 _ _ a1') ( uu1.pr21 _ _ a1) -> uu1.paths _ a1' a1). intros.  set (X':=  uu1.maponpaths _ _ ( uu1.pr21 _ _ ) _ _ X). 
assert (is:  uu1.isweq _ _ h).  apply ( uu1.isweqpr21pr21). apply ( uu1.pathsweq2 _ _ h is _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:= uu1.gradth _ _ _ _ egf efg). 
apply ( uu1.isweqtotaltofib _ P1 P2  (fun XY: uu1.dirprod hProp hProp => (match XY with  uu1.tpair X Y => eqweqmaphProp X Y end)) is2 ( uu1.dirprodpair _ _ P P')). Defined. 

Corollary uu1isasethProp : uu1.isaset hProp.
Proof. unfold isaset.  simpl. intro. intro. apply (uu1.isofhlevelweqb (S O) _ _ _ (univfromtwoaxiomshProp x x') (uu1.isapropweq x x' (uu1.pr22 _ _ x'))). Defined.



(* End of the file univalence_for_hProp.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)