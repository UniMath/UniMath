Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.products.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

Local Open Scope cat.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context {C_finite_products : finite_products C}.
  Variable (X : C).

  (* Construct an algebraic theory as an abstract clone *)
  Definition endomorphism_clone_data : abstract_clone_data.
  Proof.
    use make_abstract_clone_data.
    - use make_algebraic_base.
      + intro n.
        pose (power := ProductObject _ _ (C_finite_products n (λ _, X))).
        exact (homset power X).
      + intros m n f g.
        exact (f ∘ (ProductArrow _ _ _ g)).
    - intro n.
      apply ProductPr.
  Defined.

  Definition endomorphism_is_clone : is_abstract_clone endomorphism_clone_data.
  Proof.
    use make_is_abstract_clone.
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
    := algebraic_theory_weq_abstract_clone (make_abstract_clone _ endomorphism_is_clone).

End EndomorphismAlgebraicTheory.