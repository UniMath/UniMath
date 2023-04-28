Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebraMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition algebraic_theory_algebra_data_full_disp_cat
  : disp_cat (cartesian algebraic_theory_cat HSET).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : hSet).
    exact (∏ n, (T n : hSet) → (stn n → A) → A).
  - intros X X' action action' Y.
    pose (A := make_algebraic_theory_algebra_data (pr2 X) action).
    pose (A' := make_algebraic_theory_algebra_data (pr2 X') action').
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : A → A').
    exact (∏ n f a, G (action n f a) = action' n (F _ f) (λ i, G (a i))).
  - intros A A' action action' F.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - intros x action n f a.
    pose (A := pr2 x : hSet).
    assert (H : pr2 (identity x) = identity (A : HSET)).
    + apply (eqtohomot (transportf_const _ (A → A))).
    + now rewrite H.
  - intros x x' x'' action action' action'' y y' Gcommutes G'commutes n f a.
    pose (A := pr2 x : hSet).
    pose (A' := pr2 x' : hSet).
    pose (A'' := pr2 x'' : hSet).
    pose (G := pr2 y : A → A').
    pose (G' := pr2 y' : A' → A'').
    assert (H : pr2 (y · y') = (G : HSET⟦A, A'⟧) · G').
    + apply (eqtohomot (transportf_const _ (A → A''))).
    + rewrite H.
      unfold compose.
      simpl.
      now rewrite Gcommutes, G'commutes.
Defined.

Definition algebraic_theory_algebra_data_full_cat : category
  := total_category algebraic_theory_algebra_data_full_disp_cat.

Definition algebraic_theory_algebra_full_disp_cat : disp_cat algebraic_theory_algebra_data_full_cat.
Proof.
  use disp_struct.
  - intro x.
    pose (A := make_algebraic_theory_algebra_data (pr21 x) (pr2 x)).
    exact (is_algebraic_theory_algebra A).
  - exact (λ _ _ _ _ _, unit).
  - intros.
    exact isapropunit.
  - intros.
    exact tt.
  - intros.
    exact tt.
Defined.

Definition algebraic_theory_algebra_full_cat : category
  := total_category algebraic_theory_algebra_full_disp_cat.

Definition algebraic_theory_algebra_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat algebraic_theory_algebra_full_disp_cat).

Definition algebraic_theory_algebra_cat
  (T : algebraic_theory)
  := fiber_category algebraic_theory_algebra_disp_cat T.
