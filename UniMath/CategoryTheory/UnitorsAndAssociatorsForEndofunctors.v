(** **********************************************************

Benedikt Ahrens, Ralph Matthes

2015

Modified by: Anders Mörtberg, 2016
             Ralph Matthes, 2017

************************************************************)


(** **********************************************************

Contents :

- Definition of the (weak) monoidal structure on endofunctors
  (however, the definitions are not confined to endofunctors)

  Here, we only give the unitors and associators and do not
  build a monoidal category (anyway, this is not possible
  since we are not considering only endofunctors).


************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.

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

Goal ∏ X Y : C ⟶ D, functor_composite X (functor_identity D) ⟹ Y = (X ⟹ Y).
Proof.
  intros X Y.
  apply idpath.
Qed.

(** this also holds in the target but is not needed here *)
Goal ∏ X Y : C ⟶ D, Y ⟹ functor_composite X (functor_identity D) = (Y ⟹ X).
Proof.
  intros X Y.
  apply idpath.
Qed.

Goal ∏ X : C ⟶ D, functor_composite (functor_identity C) X = X.
Proof.
  intros.
  apply idpath.
Qed.

(** trivially, this observed convertibility implies the following three convertibilities *)
Goal ∏ X Y : C ⟶ D, functor_composite (functor_identity C) X ⟹ Y = (X ⟹ Y).
Proof.
  intros X Y.
  apply idpath.
Qed.

(** again, this also holds in the target but is not needed here *)
Goal ∏ X Y : C ⟶ D, Y ⟹ functor_composite (functor_identity C) X = (Y ⟹ X).
Proof.
  intros X Y.
  apply idpath.
Qed.

Goal ∏ (E: precategory)(hs: has_homsets D)(H: functor [C,D,hs] E) (X: C ⟶ D),
         H(functor_composite (functor_identity C) X) = H X.
Proof.
  intros.
  apply idpath.
Qed.
(** end of implied convertibilities *)

(** the last convertibility fails for the composition with the identity as second argument *)
Goal ∏ (E: precategory)(hs: has_homsets D)(H: functor [C,D,hs] E) (X: C ⟶ D),
         H(functor_composite X (functor_identity D)) = H X.
Proof.
  intros.
  Fail (apply idpath).
Abort.
(** in particular, there is no convertibility between the arguments to [H] *)


Definition ρ_functors (X : functor C D) :
  nat_trans (functor_composite X (functor_identity D)) X := nat_trans_id X.

Definition ρ_functors_inv (X : functor C D) :
  nat_trans X (functor_composite X (functor_identity D)) := nat_trans_id X.

Definition λ_functors (X : functor C D) :
  nat_trans (functor_composite (functor_identity C) X) X := nat_trans_id X.

Definition λ_functors_inv (X : functor C D) :
  nat_trans X (functor_composite (functor_identity C) X) := nat_trans_id X.


Context {E F: precategory}.

Goal ∏ (X : functor C D)(Y : functor D E)(Z : functor E F) (U: functor C F),
  (functor_composite (functor_composite X Y) Z) ⟹ U =
  (functor_composite X (functor_composite Y Z)) ⟹ U.
Proof.
  intros.
  apply idpath.
Qed.

Goal ∏ (X : functor C D)(Y : functor D E)(Z : functor E F) (U: functor C F),
  U ⟹ (functor_composite (functor_composite X Y) Z) =
  U ⟹ (functor_composite X (functor_composite Y Z)).
Proof.
  intros.
  apply idpath.
Qed.

Definition α_functors (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite (functor_composite X Y) Z)
            (functor_composite X (functor_composite Y Z)) := nat_trans_id ((X ∙ Y) ∙ Z).

Definition α_functors_inv (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite X (functor_composite Y Z))
            (functor_composite (functor_composite X Y) Z) := nat_trans_id ((X ∙ Y) ∙ Z).

Lemma α_functors_pointwise_is_z_iso (hsF: has_homsets F)(X : functor C D)(Y : functor D E)(Z : functor E F) :
  is_z_isomorphism(C:= functor_precategory C F hsF) (α_functors X Y Z).
Proof.
  exists (α_functors_inv X Y Z).
  split; apply nat_trans_eq; try assumption; intro c; apply id_left.
Defined.

(** as a motivation, we show here that, propositionally, the functors in source and target of these
    are equal, for each of the three pairs of functors; the extra assumption on having homsets is only used in order
    to have simple proofs, it is not necessary, as shown below *)
Local Lemma motivation_ρ_functors (hsD : has_homsets D)(X : functor C D) : functor_composite X (functor_identity D) = X.
Proof.
  now apply (functor_eq _ _ hsD); induction X as [data laws]; induction data as [onobs onmorphs].
Qed.

Local Lemma motivation_λ_functors (hsD : has_homsets D)(X : functor C D) : functor_composite (functor_identity C) X = X.
Proof.
  now apply (functor_eq _ _ hsD); induction X as [data laws]; induction data as [onobs onmorphs].
Qed.

Local Lemma motivation_α_functors (hsF : has_homsets F)(X : functor C D)(Y : functor D E)(Z : functor E F) :
  functor_composite (functor_composite X Y) Z = functor_composite X (functor_composite Y Z).
Proof.
  now apply (functor_eq _ _ hsF); induction X as [data laws]; induction data as [onobs onmorphs].
Qed.

(** these laws do not help in type-checking definitions which is why the transformations further above are needed *)


(** now we get rid of the homset assumptions by using results of Section "functor_equalities" in
    UniMath.CategoryTheory.Core.Functors.v *)

Local Lemma motivation_ρ_functors_stronger (X : functor C D) : functor_composite X (functor_identity D) = X.
Proof.
  apply functor_identity_right.
Qed.

Local Lemma motivation_λ_functors_stronger (X : functor C D) : functor_composite (functor_identity C) X = X.
Proof.
  apply functor_identity_left.
Qed.

Local Lemma motivation_α_functors_stronger (X : functor C D)(Y : functor D E)(Z : functor E F) :
  functor_composite (functor_composite X Y) Z = functor_composite X (functor_composite Y Z).
Proof.
  apply functor_assoc.
Qed.


End Monoidal_Structure_on_Endofunctors.
