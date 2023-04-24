Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition algebraic_theory_algebra_data_disp_cat (T : algebraic_theory_data) : disp_cat HSET.
Proof.
  use disp_struct.
  - exact (λ (A : hSet), ∏ n, (T n : hSet) → (stn n → A) → A).
  - intros A A' action action' F.
    exact (∏ n f a, F (action n f a) = action' n f (λ i, F (a i))).
  - intros A A' action action' F.
    simpl.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - now intros.
  - intros A A' A'' action action' action'' F F' Fcommutes F'commutes n f a.
    unfold compose.
    simpl.
    now rewrite Fcommutes, F'commutes.
Defined.

Definition algebraic_theory_algebra_data_cat (T : algebraic_theory_data) : category := total_category (algebraic_theory_algebra_data_disp_cat T).

Definition algebraic_theory_algebra_disp_cat (T : algebraic_theory_data) : disp_cat (algebraic_theory_algebra_data_cat T).
Proof.
  use disp_struct.
  - exact is_algebraic_theory_algebra.
  - exact (λ _ _ _ _ _, unit).
  - intros.
    exact isapropunit.
  - intros.
    exact tt.
  - intros.
    exact tt.
Defined.

Definition algebraic_theory_algebra_cat (T : algebraic_theory_data) : category := total_category (algebraic_theory_algebra_disp_cat T).
