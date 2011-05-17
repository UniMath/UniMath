(** * Generalities on [ hProp ] requiring resizing. 

This is the addendum to the file hProp which contains results requiring the resizing axiom. At the moment one needs a Type in Type patch to compile it. The resizing axioms which we need here is as follows:

RA1  if [ X : UU1 ] and [ uu1.isaprop X ] are valid then  [ X : UU0 ] is valid.   
 
*)

(** *** Preambule *)

Add Rec LoadPath "../Generalities".


Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** *** Imports. *)


Require Export hProp.


(** *** [ ishinh ] with values in [ hProp ]. *) 

Theorem isapropishinh (X : UU0) : isaprop (ishinh X). 
Proof. intro. apply impred. intro x. apply impred.  intro. apply ((uu1.pr22 _ _ x)). Defined.  


Definition ishinh_hprop (X : UU0) := hProppair (ishinh X) (isapropishinh X).
Canonical Structure ishinh_hprop.

Definition hexists (X:UU0) (P: X -> hProp) : hProp := ishinh_hprop (total2 X P).


Theorem hinhuniv2 ( X Y : UU0 ) ( f : X -> ishinh Y ) : ( ishinh X ) -> ( ishinh Y ).
Proof. intros X Y f X0. apply ( hinhuniv X ( ishinh_hprop Y ) ).  assumption. assumption. Defined. 



Definition hdisj (P Q : hProp) : hProp :=  ishinh_hprop (coprod P Q).
Canonical Structure hdisj.


(** *** Proof of the only non-trivial axiom of intuitionistic logic for our constructions. For the full list of axioms see e.g.  http://plato.stanford.edu/entries/logic-intuitionistic/ *)

Theorem hconjtohdisj (P Q R : hProp) :  hconj (himpl P R) (himpl Q R) -> (himpl (hdisj P Q) R).
Proof.  intros P Q R X0. 
assert (s1: (hdisj P Q) -> R). intro X1.  
assert (s2: (coprod P Q) -> R). intro X2. destruct X2 as [ XP | XQ ].  apply X0. assumption. apply (pr22 _ _ X0).  assumption. 
apply (hinhuniv (coprod P Q) R s2). assumption.  unfold himpl. assumption.  Defined.




(* End of file hProp.v *) 


