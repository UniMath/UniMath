
(** This file contains the proof of functional extensionality for dependent functions. More precisely we prove, using the univalence axiom, a theorem funcontr which is of the same type as the axiom funcontr used in univ.v.

This proof requires one to use the univalence axiom both for the universe for which funcontr is being proved and for the universe which is one level higher. Since Coq8.3 does not have a support for universe polymorphic definitions  we have to repeat the same code several times using files u0.v, u1.v, u2.v for the code which needs to be repeated three times and u01.v and u12.v for the  code which needs to be repeated twice. 
See also the introductory comment to u01.v . 

*)


(** * Preamble. *)

Unset Automatic Introduction.

Require Export u12 u01.

Definition UU2:=u2.UU.



(** * Theorem saying that if all members of a family are contractible then the space of sections of the family is contractible. *)


Lemma iscontrtounit (T:UU0) :iscontr (T -> unit).
Proof. intros. set (cntr:= (fun t:T => tt)). split with cntr. intros. assert (e: forall f1: T -> unit, forall t:T,  paths _ (f1 t) tt). intros. induction (f1 t0). apply idpath. apply (funextfun T unit t cntr (e t)). Defined. 


Lemma ifcontrthenunit: forall T:UU0, (iscontr T) -> u1.paths _ T unit. 
Proof. intros.  apply isweqcontrtounit in X. apply weqtopaths in X. assumption. Defined. 



Theorem funcontr (T:UU0) (P: T -> UU0) (is: forall t:T, iscontr (P t)): iscontr (forall t:T, P t).
Proof. intros. assert (e: u1.paths _ P (fun t:T => unit)). apply (u12.funextfun _ _ P (fun t:T => unit) (fun t:T => ifcontrthenunit _ (is t))). assert (e': u1.paths _ (forall t:T, P t) (forall t:T, unit)). apply (u1.maponpaths _ _ (fun Q:T->UU0 => forall t:T, Q t) _ _ e).
assert (int: iscontr (forall t:T, unit)). apply iscontrtounit. induction e'. assumption. Defined. 




(* End of the file u012.v *)

