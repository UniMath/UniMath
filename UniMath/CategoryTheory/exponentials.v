Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section exponentials.

Context {C : precategory} (PC : Products C).

(* The functor "a * _" and "_ * a" *)
Definition constprod_functor1 (a : C) : functor C C :=
  product_functor C C PC (constant_functor C C a) (functor_identity C).

Definition constprod_functor2 (a : C) : functor C C :=
  product_functor C C PC (functor_identity C) (constant_functor C C a).

Definition nat_trans_constprod_functor1 (a : C) :
  nat_trans (constprod_functor1 a) (constprod_functor2 a).
Proof.
mkpair.
- intro x; simpl; unfold product_functor_ob; simpl.
  apply ProductArrow; [ apply ProductPr2 | apply ProductPr1 ].
- abstract (intros x y f; simpl; unfold product_functor_mor; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithProductArrow|];
  now rewrite (ProductOfArrowsPr2 C _ (PC a x)), (ProductOfArrowsPr1 C _ (PC a x))).
Defined.

Definition nat_trans_constprod_functor2 (a : C) :
  nat_trans (constprod_functor2 a) (constprod_functor1 a).
Proof.
mkpair.
- intro x; simpl; unfold product_functor_ob; simpl.
  apply ProductArrow; [ apply ProductPr2 | apply ProductPr1 ].
- abstract (intros x y f; simpl; unfold product_functor_mor; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithProductArrow|];
  now rewrite (ProductOfArrowsPr2 C _ (PC x a)), (ProductOfArrowsPr1 C _ (PC x a))).
Defined.

Lemma is_left_adjoint_constprod_functor2 (a : C) :
  is_left_adjoint (constprod_functor1 a) -> is_left_adjoint (constprod_functor2 a).
Proof.
admit.
Admitted.

Definition has_exponentials : UU :=
  forall (a : C), is_left_adjoint (constprod_functor1 a).

End exponentials.