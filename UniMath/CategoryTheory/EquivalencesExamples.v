Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.

Section delta_functor_adjunction.

Context {C : precategory} (PC : Products C).

(* The delta_functor is left adjoint to binproduct_functor *)
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
- abstract (split; simpl; intro x;
  [ unfold prodcatmor, compose; simpl;
    now rewrite ProductPr1Commutes, ProductPr2Commutes
  | rewrite postcompWithProductArrow, !id_left;
    apply pathsinv0, Product_endo_is_identity;
      [ apply ProductPr1Commutes | apply ProductPr2Commutes ]]).
Defined.

End delta_functor_adjunction.

Section bincoproduct_functor_adjunction.

Context {C : precategory} (PC : Coproducts C).

(* The bincoproduct_functor left adjoint to delta_functor *)
Lemma is_left_adjoint_bincoproduct_functor : is_left_adjoint (bincoproduct_functor PC).
Proof.
apply (tpair _ (delta_functor _)).
mkpair.
- split.
  + mkpair.
    * simpl; intro p; set (x := pr1 p); set (y := pr2 p).
      split; [ apply (CoproductIn1 _ (PC x y)) | apply (CoproductIn2 _ (PC x y)) ].
    * abstract (intros p q f; unfold prodcatmor, compose; simpl;
                now rewrite CoproductOfArrowsIn1, CoproductOfArrowsIn2).
  + mkpair.
    * intro x; apply (CoproductArrow _ _ (identity x) (identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithCoproductArrow, postcompWithCoproductArrow,
                            id_right, id_left).
- abstract (split; simpl; intro x;
  [ rewrite precompWithCoproductArrow, !id_right;
    apply pathsinv0, Coproduct_endo_is_identity;
      [ apply CoproductIn1Commutes | apply CoproductIn2Commutes ]
  | unfold prodcatmor, compose; simpl;
    now rewrite CoproductIn1Commutes, CoproductIn2Commutes ]).
Defined.

End bincoproduct_functor_adjunction.
