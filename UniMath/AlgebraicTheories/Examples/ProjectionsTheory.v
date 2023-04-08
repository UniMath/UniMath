(** * The initial algebraic theory, with T n = {1, ..., n} and pr i = i *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

(* Construct an algebraic theory as an abstract clone *)
Definition projections_clone_data
  : abstract_clone_data
  := make_abstract_clone_data
    (make_algebraic_base
      (λ n, (stn n ,, isasetstn n))
      (λ _ _ f g, g f))
    (λ _ i, i).

Lemma projections_is_clone : is_abstract_clone projections_clone_data.
Proof.
  now use make_is_abstract_clone;
    repeat intro.
Qed.

Definition projections_theory
  : algebraic_theory
  := algebraic_theory_weq_abstract_clone (make_abstract_clone _ projections_is_clone).
