
(** **********************************************************

Anders Mörtberg

2016

Definition of the general product category

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section dep_product_precategory.

Variable I : UU.
Variables C : I -> precategory.

Definition product_precategory_ob_mor : precategory_ob_mor.
Proof.
mkpair.
- apply (Π (i : I), ob (C i)).
- intros f g.
  apply (Π i, f i --> g i).
Defined.

Definition product_precategory_data : precategory_data.
Proof.
  exists product_precategory_ob_mor.
  split.
  - intros f i; simpl in *.
    apply (identity (f i)).
  - intros a b c f g i; simpl in *.
    exact (f i ;; g i).
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

Definition has_homsets_product_precategory (hsC : Π (i:I), has_homsets (C i)) :
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
  := product_precategory I (fun _ => C).

Definition has_homsets_power_precategory (hsC : has_homsets C) :
  has_homsets power_precategory.
Proof.
apply has_homsets_product_precategory.
intro i; assumption.
Qed.

End power_precategory.


Section functors.

Definition family_functor_data (I : UU) {A B : I -> precategory}
  (F : Π (i : I), functor (A i) (B i)) :
  functor_data (product_precategory I A)
               (product_precategory I B).
Proof.
mkpair.
- intros a i; apply (F i (a i)).
- intros a b f i; apply (# (F i) (f i)).
Defined.

Definition family_functor (I : UU) {A B : I -> precategory}
  (F : Π (i : I), functor (A i) (B i)) :
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
mkpair.
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
mkpair.
- intros x i; apply x.
- intros x y f i; simpl; apply f.
Defined.

Definition delta_functor (I : UU) (C : precategory) :
  functor C (power_precategory I C).
Proof.
apply (tpair _ (delta_functor_data I C)).
abstract (split; intros x *; apply idpath).
Defined.

End functors.