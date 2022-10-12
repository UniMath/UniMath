
(** **********************************************************

Anders Mörtberg

2016

For a specialization to binary products, see [precategory_binproduct].

Contents:

- Definition of the general product category ([product_precategory])
- Functors
  - Families of functors ([family_functor])
  - Projections ([pr_functor])
  - Delta functor ([delta_functor])
  - Tuple functor ([tuple_functor])
- Equivalence between functors into components and functors into product

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Local Open Scope cat.

Section dep_product_precategory.

  Context {I : UU} (C : I -> category).

  Definition product_precategory_ob_mor : precategory_ob_mor.
  Proof.
  use tpair.
  - apply (∏ (i : I), ob (C i)).
  - intros f g.
    apply (∏ i, f i --> g i).
  Defined.

  Definition product_precategory_data : precategory_data.
  Proof.
    exists product_precategory_ob_mor.
    split.
    - intros f i; simpl in *.
      apply (identity (f i)).
    - intros a b c f g i; simpl in *.
      exact (f i · g i).
  Defined.

  Lemma is_precategory_product_precategory_data :
    is_precategory product_precategory_data.
  Proof.
    repeat split; intros; apply funextsec; intro i.
    - apply id_left.
    - apply id_right.
    - apply assoc.
    - apply assoc'.
  Defined. (** needed for the op-related goal below *)

  Definition product_precategory : precategory
    := tpair _ _ is_precategory_product_precategory_data.

  Definition has_homsets_product_precategory :
    has_homsets product_precategory.
  Proof.
  intros ? ?; simpl.
  apply impred_isaset; intro; apply C.
  Qed.

  Definition product_category' : category := make_category _ has_homsets_product_precategory.

End dep_product_precategory.



(** The product of categories is again a category. *)
Definition product_category {I : UU} (C : I -> category) : category.
  use make_category.
  - exact (product_precategory C).
  - apply has_homsets_product_precategory.
Defined.

Section power_precategory.
  Context (I : UU) (C : category).

  Definition power_category : category
    := @product_category I (λ _, C).

End power_precategory.

(** ** Functors *)

(* TODO: Some of the functors in this section can be defined in terms of each other *)
Section functors.

(** *** Families of functors ([family_functor]) *)

Definition family_functor_data (I : UU) {A B : I -> category}
  (F : ∏ (i : I), (A i) ⟶ (B i)) :
  functor_data (product_category A)
               (product_category B).
Proof.
use tpair.
- intros a i; apply (F i (a i)).
- intros a b f i; apply (# (F i) (f i)).
Defined.

Definition family_functor (I : UU) {A B : I -> category}
  (F : ∏ (i : I), (A i) ⟶ (B i)) :
  (product_category A) ⟶ (product_category B).
Proof.
apply (tpair _ (family_functor_data I F)).
abstract
  (split; [ intro x; apply funextsec; intro i; simpl; apply functor_id
          | intros x y z f g; apply funextsec; intro i; apply functor_comp]).
Defined.

(** *** Projections ([pr_functor]) *)

Definition pr_functor_data (I : UU) (C : I -> category) (i : I) :
  functor_data (product_category C) (C i).
Proof.
use tpair.
- intro a; apply (a i).
- intros x y f; simpl; apply (f i).
Defined.

Definition pr_functor (I : UU) (C : I -> category) (i : I) :
  (product_category C) ⟶ (C i).
Proof.
apply (tpair _ (pr_functor_data I C i)).
abstract (split; intros x *; apply idpath).
Defined.

(** *** Delta functor ([delta_functor]) *)

Definition delta_functor_data (I : UU) (C : category) :
  functor_data C (power_category I C).
Proof.
use tpair.
- intros x i; apply x.
- intros x y f i; simpl; apply f.
Defined.

Definition delta_functor (I : UU) (C : category) :
  C ⟶ (power_category I C).
Proof.
apply (tpair _ (delta_functor_data I C)).
abstract (split; intros x *; apply idpath).
Defined.

(** *** Tuple functor ([tuple_functor]) *)

Definition tuple_functor_data {I : UU} {A : category} {B : I → category}
  (F : ∏ i, A ⟶ (B i)) : functor_data A (product_category B).
Proof.
use tpair.
- intros a i; exact (F i a).
- intros a b f i; exact (# (F i) f).
Defined.

Lemma tuple_functor_axioms {I : UU} {A : category} {B : I → category}
  (F : ∏ i, A ⟶ (B i)) : is_functor (tuple_functor_data F).
Proof.
split.
- intros a. apply funextsec; intro i. apply functor_id.
- intros ? ? ? ? ?. apply funextsec; intro i. apply functor_comp.
Qed.

Definition tuple_functor {I : UU} {A : category} {B : I → category}
  (F : ∏ i, A ⟶ (B i)) : A ⟶ (product_category B)
    := (tuple_functor_data F,, tuple_functor_axioms F).

Lemma pr_tuple_functor {I : UU} {A : category} (B : I → category)
  (F : ∏ i, A ⟶ (B i)) (i : I) : tuple_functor F ∙ pr_functor I B i = F i.
Proof.
  apply functor_eq.
  apply (B i).
  apply idpath.
Qed.

End functors.

(** ** Equivalence between functors into components and functors into product *)

(** This is a phrasing of the universal property of the product, compare to
    [weqfuntoprodtoprod]. *)
Lemma functor_into_product_weq {I : UU} {A : category} {B : I → category} :
  A ⟶ (product_category B) ≃ (∏ i : I, A ⟶ (B i)).
Proof.
  use weq_iso.
  - intros ? i.
    (** Compose A ⟶ product_precategory I B ⟶ B i *)
    apply (functor_composite (C' := product_precategory B)).
    + assumption.
    + exact (pr_functor _ _ i).
  - exact tuple_functor.
  - intro y.
    apply functor_eq; [apply homset_property|].
    reflexivity.
  - intro f; cbn.
    apply funextsec; intro i.
    apply functor_eq; [exact (homset_property (B i))|].
    reflexivity.
Defined.
