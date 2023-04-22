(** * The initial algebraic theory, with T n = {1, ..., n} and pr i = i *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras.

Definition projections_theory : algebraic_theory.
Proof.
  use (make_algebraic_theory' stnset (λ _ i, i) (λ _ _ f g, g f)).
  all: (abstract now repeat intro).
Defined.

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
