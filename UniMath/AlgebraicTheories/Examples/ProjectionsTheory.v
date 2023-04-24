(** * The initial algebraic theory, with T n = {1, ..., n} and pr i = i *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.

Definition projections_theory'_data
  : algebraic_theory'_data
  := make_algebraic_theory'_data
      stnset
      (λ _ i, i)
      (λ _ _ f g, g f).

Lemma projections_is_theory' : is_algebraic_theory' projections_theory'_data.
Proof.
  now use make_is_algebraic_theory';
    repeat intro.
Qed.

Definition projections_theory
  : algebraic_theory
  := make_algebraic_theory' _ projections_is_theory'.

Definition projections_theory_algebra_data (A : hSet)
  : algebraic_theory_algebra_data projections_theory
  := make_algebraic_theory_algebra_data A (λ n (i : (projections_theory n : hSet)) f, f i).

Lemma projections_theory_algebra_is_algebra (A : hSet)
  : is_algebraic_theory_algebra (projections_theory_algebra_data A).
Proof.
  use make_is_algebraic_theory_algebra;
    now repeat intro.
Qed.

Definition projections_theory_algebra (A : hSet)
  : algebraic_theory_algebra projections_theory
  := make_algebraic_theory_algebra _ (projections_theory_algebra_is_algebra A).
