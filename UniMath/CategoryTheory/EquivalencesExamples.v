(**

This file contains some adjunctions:

- The delta_functor is left adjoint to binproduct_functor
- The bincoproduct_functor left adjoint to delta_functor

Written by: Anders Mörtberg, 2016

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.ArbitraryProductPrecategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.arbitrary_products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.

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

Section arbitrary_delta_functor_adjunction.

Context (I : UU) {C : precategory} (PC : ArbitraryProducts I C).

Lemma is_left_adjoint_arbitrary_delta_functor :
  is_left_adjoint (arbitrary_delta_functor I C).
Proof.
apply (tpair _ (arbitrary_product_functor _ PC)).
mkpair.
- split.
  + mkpair.
    * simpl; intro x.
      apply (ArbitraryProductArrow _ _ _ (fun _ => identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithArbitraryProductArrow, id_right,
                            postcompWithArbitraryProductArrow, id_left).
  + mkpair.
    * intros x i; apply ArbitraryProductPr.
    * abstract (intros p q f; apply funextsec; intro i; unfold compose; simpl;
                now rewrite ArbitraryProductOfArrowsPr).
- abstract (split; simpl; intro x;
    [ apply funextsec; intro i; apply (ArbitraryProductPrCommutes _ _ (fun _ => x))
    | rewrite postcompWithArbitraryProductArrow;
      apply pathsinv0, ArbitraryProduct_endo_is_identity; intro i;
      eapply pathscomp0; [|apply (ArbitraryProductPrCommutes I C _ (PC x))];
      apply cancel_postcomposition, maponpaths, funextsec; intro j; apply id_left]).
Defined.

End arbitrary_delta_functor_adjunction.

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

Section arbitrary_coproduct_functor_adjunction.

Context (I : UU) {C : precategory} (PC : ArbitraryCoproducts I C).

Lemma is_left_adjoint_arbitrary_indexed_coproduct_functor :
  is_left_adjoint (arbitrary_indexed_coproduct_functor I PC).
Proof.
apply (tpair _ (arbitrary_delta_functor _ _)).
mkpair.
- split.
  + mkpair.
    * intros p i; apply ArbitraryCoproductIn.
    * abstract (intros p q f; apply funextsec; intro i; unfold compose; simpl;
                now rewrite ArbitraryCoproductOfArrowsIn).
  + mkpair.
    * intro x; apply (ArbitraryCoproductArrow _ _ _ (fun _ => identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithArbitraryCoproductArrow,
                            postcompWithArbitraryCoproductArrow,
                            id_right, id_left).
- abstract (split; simpl; intro x;
    [ rewrite precompWithArbitraryCoproductArrow;
      apply pathsinv0, ArbitraryCoproduct_endo_is_identity; intro i;
      eapply pathscomp0; [|apply ArbitraryCoproductInCommutes];
      apply maponpaths, maponpaths, funextsec; intro j; apply id_right
    | apply funextsec; intro i; apply (ArbitraryCoproductInCommutes _ _ (fun _ => x))]).
Defined.

End arbitrary_coproduct_functor_adjunction.
