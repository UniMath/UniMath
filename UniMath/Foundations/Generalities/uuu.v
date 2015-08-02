(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011 

This is the first in the group of files which contain the (current state of) the mathematical library for the proof assistant Coq based on the Univalent Foundations. 
It contains some new notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)




(** Preamble. *)

Unset Automatic Introduction.  (** This line has to be removed for the file to compile with Coq8.2 *)

(** Universe structure *)

Notation UUU := Set .

(** Empty type.  The empty type is introduced in Coq.Init.Datatypes by the line:

[ Inductive Empty_set : Set := . ]

*)

Notation empty := Empty_set. 
Notation empty_rect := Empty_set_rect. 

(** Identity Types. Identity types are introduced in Coq.Init.Datatypes by the lines : 

[ Inductive identity ( A : Type ) ( a : A ) : A -> Type := identity_refl : identity _ a a .    
    
Hint Resolve identity_refl : core . ] 

*)

Inductive paths {A:Type} (a:A) : A -> Type := paths_refl : paths a a.
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl .

(* Remark: all of the uu0.v now uses only paths_rect and not the direct "match" construction
on paths. By adding a constantin paths for the computation rule for paths_rect and then making
both this constant and paths_rect itself opaque it is possible to check which of the
constructions of the uu0 can be done with the weakened version of the Martin-Lof Type Theory
that is interpreted by the Bezm-Coquand-Huber cubical set model of 2014. *)




(** Coproducts . 

The coproduct of two types is introduced in Coq.Init.Datatypes by the lines:

[ Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B. ]
*)

Notation coprod := sum .

Notation ii1fun := inl .
Notation ii2fun := inr .

Notation ii1 := inl .
Notation ii2 := inr .
Implicit Arguments ii1 [ A B ] .
Implicit Arguments ii2 [ A B ] .

Notation coprod_rect := sum_rect.



(** Dependent sums. 

One can not use a new record each time one needs it because the general theorems about this 
construction would not apply to new instances of "Record" due to the "generativity" of inductive 
definitions in Coq. 

We use "Inductive" instead of "Record" here. 
Using "Record" which is equivalent to "Structure" would allow us later to use the mechanism of 
canonical structures with total2. 
By using "Structure", we could also get eta for dependent pairs, by adding the option 
"Set Primitive Projections.".
*)


Inductive total2 { T: Type } ( P: T -> Type ) := tpair : forall ( t : T ) ( p : P t ) , total2 P . 
Arguments tpair {T} _ _ _.

Definition pr1 ( T : Type ) ( P : T -> Type ) ( t : total2 P ) : T .
Proof . intros .  induction t as [ t p ] . exact t . Defined. 

Arguments pr1 {_ _} _.

Definition pr2 ( T : Type ) ( P : T -> Type ) ( t : total2 P ) : P ( pr1 t ) .
Proof . intros .  induction t as [ t p ] . exact p . Defined. 

Arguments pr2 {_ _} _.



(*

(** The phantom type family ( following George Gonthier ) *)

Inductive Phant ( T : Type ) := phant : Phant T .


*)

(** The following command checks wheather the patch which modifies the universe level assignement for inductive types have been installed. With the patch it returns [ paths 0 0 : UUU ] . Without the patch it returns [ paths 0 0 : Prop ]. *)

Check (O = O) .




(* End of the file uuu.v *)
