Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.limits.products.

Section delta_functor_adjunction.

Context {C : precategory} (PC : Products C).

Lemma is_left_adjoint_delta_functor : is_left_adjoint (delta_functor C).
Proof.
apply (tpair _ (binproduct_functor PC)).
mkpair.
- split.
  + mkpair.
    * simpl; intro x.
      apply (ProductArrow _ _ (identity x) (identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithProductArrow, id_right, postcompWithProductArrow, id_left).
  + mkpair.
    * simpl; intro x; split; [ apply ProductPr1 | apply ProductPr2 ].
    * abstract (intros p q f; unfold prodcatmor, compose; simpl;
                now rewrite ProductOfArrowsPr1, ProductOfArrowsPr2).
- split; simpl; intro x.
  + unfold prodcatmor, compose; simpl.
    now rewrite ProductPr1Commutes, ProductPr2Commutes.
  + rewrite postcompWithProductArrow, !id_left.
    apply pathsinv0, Product_endo_is_identity; [ apply ProductPr1Commutes | apply ProductPr2Commutes ].
Defined.

End delta_functor_adjunction.
