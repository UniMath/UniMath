(** *  Set quotients. Construction 2. 


****************** THIS FILE IS UNFINISHED ******************


The following construction of the set quotient is based on the following idea. Let X be a set. Then we have the obvious "double evaluation map" from X to the product over all sets Y of the sets ((X -> Y) -> Y). This is always an inclusion and in particular X is isomorphic to the image of this map. Suppore now we have a relation (which need not be an equivalence relation) R on X. Then we know that (X/R -> Y) is a subset of (X -> Y) which consists of functions compatible with the relation even if we do not know what X/R is. Thus we may consider the image of X in the product over all Y of ((X/R -> Y) ->Y) and it must be isomorphic to X/R. This ideas are realized in the definitions given below. There are two advantages to this approach. One is that the relation need not be an equivalence relation. Another one is that it can be more easily generalized to the higher quotients of type.


We also show that two constructions of set-quotients of types - the one given in set_quotients and the one given here agree up to an isomorphism (weak equivalence). *)






(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export set_quotients_r_up.




(** *** Functions compatible with a relation *)

Definition compfun (X:UU0)(R: hrel X)(S : hSet) : UU0 := total2 (X -> S) (fun F: X -> S => forall x x' : X, R x x' -> paths _ (F x ) (F x')).
Definition compfunpair (X:UU0) (R: hrel X)(S : hSet) := tpair (X -> S) (fun F: X -> S => forall x x' : X, R x x' -> paths _ (F x ) (F x')).

Definition compevmap (X:UU0)(R: hrel X) : X -> forall S: hSet, (compfun X R S) -> S := fun x:X => fun S:_ => fun f: compfun X R S => pr21 _ _ f x.




(** *** The quotient set of a type by a relation. *)

Definition setquot2 (X:UU0)(R: hrel X) : UU0 := image _ _ (compevmap X R). (* We will be asuming below that setquot2 is in UU0.  In the future it should be proved using [ issurjsetquot2pr ] below and a resizing axiom. The appropriate resizing axiom for this should say that if X -> Y is a surjection, Y is an hset and X:UU then Y:UU . *)  

Definition setquot2pr (X:UU0)(R: hrel X) : X -> setquot2 X R := fun x:X => imagepair X _ (compevmap X R) _ (hinhpr _ (hfiberpair _ _ (compevmap X R) (compevmap X R x) x (idpath _ _ ))). 

Lemma iscompsetquot2pr (X : UU0) (R : hrel X) ( x x' : X) (a: R x x') : paths _ (setquot2pr _ R x) (setquot2pr _ R x').
Proof. intros. 
assert (e1: paths _ (compevmap _ R x) (compevmap _ R x')).  apply u1pathstou0paths. apply uu1.funextsec. intro S.  apply uu1.funextsec.  intro f.   unfold compfun in f. apply u0pathstou1paths. apply (pr22 _ _ f x x' a). 
apply (invmaponpathsincl _ _ _ (isinclimageincl _ _ (compevmap X R) ) (setquot2pr X R x) (setquot2pr X R x') e1). Defined. 


Lemma issurjsetquot2pr (X : UU0) (R : hrel X) : issurjective _ _ (setquot2pr X R).
Proof. intros. apply issurjprtoimage. Defined.    

Definition setquot2univ (X : UU0) (Y : hSet) (R: hrel X) (F: X -> Y ) (iscomp : forall x x' : X, R x x' -> paths _ (F x ) (F x')) : setquot2 X R -> Y := fun q:_ => (( pr21 _ _ q Y (compfunpair _ _ Y F iscomp))).  


Theorem setquot2univcomm  (X : UU0) (Y : hSet) (R: hrel X) (F: X -> Y ) (iscomp : forall x x' : X, R x x' -> paths _ (F x ) (F x')) ( x : X) : paths _ (setquot2univ _ _ _ F iscomp ( setquot2pr X R x )) (F x).  
Proof. intros. apply idpath. Defined.  

Theorem isasetsetquot2 (X : UU0) (R: hrel X) : isaset (setquot2 X R).
Proof. intros. 
assert (is1: isaset ( forall S: hSet, (compfun X R S) -> S )). apply (u1isasettou0isaset). apply uu1.impred.  intro.  apply uu1.impred.  intro X0.  apply (u0isasettou1isaset t). apply (uu1.pr22 _ _ t).
apply (isasetsubset _  _  _ is1 (isinclimageincl _ _ _ )).  Defined. 


(** The previous results show that setquot2 as constructed is indeed the categorical quotient of X with respect to R. What we can not direcly show for this construction is that for  [ (X : UU0) (R : hrel X) ( x x' : X) ( e: paths _ (setquot2pr _ R x) (setquot2pr _ R x')) (is : iseqrel X R) ] one has [ R x x' ]. For this we will need to define setquot2 in terms of equivalence classes and then show that the two constructions agree. *)







(* *** Comparison of setquot2 and setquot.  *)



Definition setquottosetquot2 (X: UU0) (R: hrel X) (is: iseqrel _ R) : setquot X R -> setquot2 X R.
Proof. intros X R is X0. apply (setquotuniv X R (hSetpair _ (isasetsetquot2 X R)) (setquot2pr X R) (iscompsetquot2pr X R) X0).  Defined.












(* End of the file set_quotients_constr2.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)