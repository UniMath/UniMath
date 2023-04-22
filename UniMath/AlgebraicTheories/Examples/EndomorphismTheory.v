Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope cat.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context (C_finite_products : finite_products C).
  Variable (X : C).

  Definition endomorphism_theory : algebraic_theory.
  Proof.
    pose (power := λ n, ProductObject _ _ (C_finite_products n (λ _, X))).
    use make_algebraic_theory'.
    - intro n.
      exact (homset (power n) X).
    - intro.
      apply ProductPr.
    - intros m n f g.
      exact (f ∘ (ProductArrow _ _ _ g)).
    - assert (H : ∏ m n i (f : stn m → C⟦power n, X⟧),
        ProductArrow _ _ (C_finite_products _ _) f · ProductPr _ _ _ i = f i).
      {
        do 4 intro.
        exact (ProductPrCommutes _ _ _ _ _ _ _).
      }
      abstract exact H.
    - assert (H : ∏ n (f : C⟦power n, X⟧), ProductArrow _ _ _ (ProductPr _ _ _) · f = f).
      {
        do 2 intro.
        rewrite <- id_left.
        apply (maponpaths (λ x, x · _)).
        rewrite ProductArrowEta.
        apply maponpaths, funextfun.
        intro.
        apply (!id_left _).
      }
      abstract exact H.
    - assert (H : ∏ l m n (f : C⟦power l, X⟧) (g : _ → C⟦power m, X⟧) (h : _ → C⟦power n, X⟧),
        ProductArrow _ _ _ h · (ProductArrow _ _ _ g · f)
        = ProductArrow _ _ _ (λ i, ProductArrow _ _ _ h · g i) · f).
      {
        simpl.
        intros l m n f_l f_m f_n.
        simpl.
        rewrite assoc.
        apply (maponpaths (λ f, f · f_l)).
        rewrite (ProductArrowEta _ _ _ _ _ (_ · _)).
        apply maponpaths, funextfun.
        intro.
        rewrite assoc'.
        apply maponpaths.
        exact (ProductPrCommutes _ _ _ _ _ _ _).
      }
      abstract exact H.
  Defined.

End EndomorphismAlgebraicTheory.

Definition set_endomorphism_theory
  (X : hSet)
  : algebraic_theory
  := endomorphism_theory (λ n, ProductsHSET (stn n)) (X : ob HSET).
