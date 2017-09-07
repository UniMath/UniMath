(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015

Modified by: Anders Mörtberg, 2016
             Ralph Matthes, 2017

************************************************************)


(** **********************************************************

Contents :

- Definition of the (weak) monoidal structure on endofunctors
  (however, the definitions are not confined to endofunctors)


************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** There is a monoidal structure on endofunctors, given by composition. While
    this is considered to be strict in set-theoretic category theory, it ain't
    strict in type theory with respect to convertibility. So we consider it to
    be a weak monoidal structure instead. However, pointwise, it suffices to
    take the identity for all those natural transformations (the identity is
    also behind the definition of nat_trans_functor_assoc).

    To understand the need for this structure even better, notice that the
    proofs of functor axioms for one composition in the unitality and
    associativity properties are slightly different from the proofs for the other
    and because of it the composition of functors is not strictly unital or
    associative. However, these proofs are not used in the definition of natural
    transformations, to be precise only functor_data is used, and the
    composition of functor_data is strictly unital and associative.

*)
Section Monoidal_Structure_on_Endofunctors.

(** while this is normally used for endofunctors, it can be done more generally,
    but already for endofunctors, this is crucial for the development of substitution systems *)

Context {C D : precategory}.

Definition ρ_functor (X : functor C D) :
  nat_trans (functor_composite X (functor_identity D)) X := nat_trans_functor_id_right X.

Definition ρ_functor_inv (X : functor C D) :
  nat_trans X (functor_composite X (functor_identity D)) := ρ_functor X.

Definition λ_functor (X : functor C D) :
  nat_trans (functor_composite (functor_identity C) X) X := ρ_functor X.

Definition λ_functor_inv (X : functor C D) :
  nat_trans X (functor_composite (functor_identity C) X) := ρ_functor X.


Context {E F: precategory}.

Definition α_functor (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite (functor_composite X Y) Z)
            (functor_composite X (functor_composite Y Z)) := nat_trans_functor_assoc X Y Z.

Definition α_functor_inv (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite X (functor_composite Y Z))
            (functor_composite (functor_composite X Y) Z) := α_functor X Y Z.



(** as a motivation, we show here that, propositionally, both functors are equal, for each
    of the three pairs of functors; the extra assumption on having homsets is only used in order
    to have simple proofs, it is not necessary, as shown in Section "functor_equalities" in
    functor_categories.v: Lemmas functor_identity_left, functor_identity_right and functor_assoc *)
Local Lemma motivation_ρ_functor (hsD : has_homsets D)(X : functor C D) : functor_composite X (functor_identity D) = X.
Proof.
  now apply (functor_eq _ _ hsD); induction X as [data laws]; induction data as [onobs onmorphs].
Defined.

Local Lemma motivation_λ_functor (hsD : has_homsets D)(X : functor C D) : functor_composite (functor_identity C) X = X.
Proof.
  now apply (functor_eq _ _ hsD); induction X as [data laws]; induction data as [onobs onmorphs].
Defined.

Local Lemma motivation_α_functor (hsF : has_homsets F)(X : functor C D)(Y : functor D E)(Z : functor E F) :
  functor_composite (functor_composite X Y) Z = functor_composite X (functor_composite Y Z).
Proof.
  now apply (functor_eq _ _ hsF); induction X as [data laws]; induction data as [onobs onmorphs].
Defined.

(** these laws do not help in type-checking definitions which is why the transformations further above are needed *)

End Monoidal_Structure_on_Endofunctors.
