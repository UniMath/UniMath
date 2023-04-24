(** * The initial algebraic theory, with T n = {1, ..., n} and pr i = i *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras.

Definition projections_clone_data
  : abstract_clone_data
  := make_abstract_clone_data
      stnset
      (λ _ i, i)
      (λ _ _ f g, g f).

Lemma projections_is_clone : is_abstract_clone projections_clone_data.
Proof.
  now use make_is_abstract_clone;
    repeat intro.
Qed.

Definition projections_theory
  : algebraic_theory
  := make_algebraic_theory' _ projections_is_clone.

Definition projections_clone_algebra_data (A : hSet)
  : abstract_clone_algebra_data projections_clone
  := make_abstract_clone_algebra_data A (λ _ (i : projections_clone _) f, f i).

Lemma projections_clone_algebra_is_algebra (A : hSet)
  : is_abstract_clone_algebra (projections_clone_algebra_data A).
Proof.
  use make_is_abstract_clone_algebra;
    now repeat intro.
Qed.

Definition projections_clone_algebra (A : hSet)
  : abstract_clone_algebra projections_clone
  := make_abstract_clone_algebra _ (projections_clone_algebra_is_algebra A).
