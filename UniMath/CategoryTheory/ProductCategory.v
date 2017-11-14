
(** **********************************************************

Anders Mörtberg

2016

Contents:

- Definition of the general product category ([product_precategory])
- Tuple functor ([tuple_functor])

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Section dep_product_precategory.

Variable I : UU.
Variables C : I -> precategory.

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
Qed.

Definition product_precategory : precategory
  := tpair _ _ is_precategory_product_precategory_data.

Definition has_homsets_product_precategory (hsC : ∏ (i:I), has_homsets (C i)) :
  has_homsets product_precategory.
Proof.
intros a b; simpl.
apply impred_isaset; intro i; apply hsC.
Qed.

End dep_product_precategory.


Section power_precategory.

Variable I : UU.
Variables C : precategory.


Definition power_precategory : precategory
  := product_precategory I (λ _, C).

Definition has_homsets_power_precategory (hsC : has_homsets C) :
  has_homsets power_precategory.
Proof.
apply has_homsets_product_precategory.
intro i; assumption.
Qed.

End power_precategory.

(* TODO: Some of the functors in this section can be defined in terms of each other *)
Section functors.

Definition family_functor_data (I : UU) {A B : I -> precategory}
  (F : ∏ (i : I), functor (A i) (B i)) :
  functor_data (product_precategory I A)
               (product_precategory I B).
Proof.
use tpair.
- intros a i; apply (F i (a i)).
- intros a b f i; apply (# (F i) (f i)).
Defined.

Definition family_functor (I : UU) {A B : I -> precategory}
  (F : ∏ (i : I), functor (A i) (B i)) :
  functor (product_precategory I A)
          (product_precategory I B).
Proof.
apply (tpair _ (family_functor_data I F)).
abstract
  (split; [ intro x; apply funextsec; intro i; simpl; apply functor_id
          | intros x y z f g; apply funextsec; intro i; apply functor_comp]).
Defined.

Definition pr_functor_data (I : UU) (C : I -> precategory) (i : I) :
  functor_data (product_precategory I C) (C i).
Proof.
use tpair.
- intro a; apply (a i).
- intros x y f; simpl; apply (f i).
Defined.

Definition pr_functor (I : UU) (C : I -> precategory) (i : I) :
  functor (product_precategory I C) (C i).
Proof.
apply (tpair _ (pr_functor_data I C i)).
abstract (split; intros x *; apply idpath).
Defined.

Definition delta_functor_data (I : UU) (C : precategory) :
  functor_data C (power_precategory I C).
Proof.
use tpair.
- intros x i; apply x.
- intros x y f i; simpl; apply f.
Defined.

Definition delta_functor (I : UU) (C : precategory) :
  functor C (power_precategory I C).
Proof.
apply (tpair _ (delta_functor_data I C)).
abstract (split; intros x *; apply idpath).
Defined.

Definition tuple_functor_data {I : UU} {A : precategory} {B : I → precategory}
  (F : ∏ i, functor A (B i)) : functor_data A (product_precategory I B).
Proof.
use tpair.
- intros a i; exact (F i a).
- intros a b f i; exact (# (F i) f).
Defined.

Lemma tuple_functor_axioms {I : UU} {A : precategory} {B : I → precategory}
  (F : ∏ i, functor A (B i)) : is_functor (tuple_functor_data F).
Proof.
split.
- intros a. apply funextsec; intro i. apply functor_id.
- intros ? ? ? ? ?. apply funextsec; intro i. apply functor_comp.
Qed.

Definition tuple_functor {I : UU} {A : precategory} {B : I → precategory}
  (F : ∏ i, functor A (B i)) : functor A (product_precategory I B)
    := (tuple_functor_data F,, tuple_functor_axioms F).

Lemma pr_tuple_functor {I : UU} {A : precategory} {B : I → precategory} (hsB : ∏ i, has_homsets (B i))
  (F : ∏ i, functor A (B i)) (i : I) : tuple_functor F ∙ pr_functor I B i = F i.
Proof.
now apply functor_eq.
Qed.

End functors.