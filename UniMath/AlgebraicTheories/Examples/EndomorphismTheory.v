(*
  Defines the endomorphism theory of an object X in some category with products, given by
  T(n) = (X^n → X). Also gives a specialization for X a set.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.

Local Open Scope cat.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context (C_finite_products : finite_products C).
  Variable (X : C).

  Definition endomorphism_theory'_data : algebraic_theory'_data.
  Proof.
    use make_algebraic_theory'_data.
    - intro n.
      pose (power := ProductObject _ _ (C_finite_products n (λ _, X))).
      exact (homset power X).
    - intro.
      apply ProductPr.
    - intros m n f g.
      exact (f ∘ (ProductArrow _ _ _ g)).
  Defined.

  Definition endomorphism_is_theory' : is_algebraic_theory' endomorphism_theory'_data.
  Proof.
    use make_is_algebraic_theory'.
    - do 4 intro.
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - do 2 intro.
      rewrite <- id_left.
      apply (maponpaths (λ x, x · _)).
      rewrite (ProductArrowEta _ _ _ _ _ (identity _)).
      apply maponpaths, funextfun.
      intro.
      symmetry.
      apply id_left.
    - intros l m n f_l f_m f_n.
      unfold comp'.
      simpl.
      rewrite assoc.
      apply (maponpaths (λ f, f · f_l)).
      rewrite (ProductArrowEta _ _ _ _ _ (_ · _)).
      apply maponpaths, funextfun.
      intro.
      rewrite assoc'.
      apply maponpaths.
      exact (ProductPrCommutes _ _ _ _ _ _ _).
  Qed.

  Definition endomorphism_theory : algebraic_theory
    := make_algebraic_theory' _ endomorphism_is_theory'.

End EndomorphismAlgebraicTheory.

Definition set_endomorphism_theory
  (X : hSet)
  : algebraic_theory
  := endomorphism_theory (λ n, ProductsHSET (stn n)) (X : ob HSET).
