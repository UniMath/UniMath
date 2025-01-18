(**************************************************************************************************

  The "one point" algebraic theory

  The trivial algebraic theory T is given by T(n) = {*}. Coincidentally, this is the terminal
  algebraic theory.

  Contents
  1. The definition of the one point theory [one_point_theory]
  2. The only algebra of the one point theory is the unit type [one_point_theory_algebra_is_trivial]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope vec_scope.

(** * 1. The definition of the one point theory *)

Definition one_point_theory_data
  : algebraic_theory_data
  := make_algebraic_theory_data
      (λ _, (unit ,, isasetunit))
      (λ _ _, tt)
      (λ _ _ _ _, tt).

Lemma one_point_is_theory : is_algebraic_theory one_point_theory_data.
Proof.
  use make_is_algebraic_theory.
  - now do 6 intro.
  - intros m n i f.
    simpl.
    now induction (f i).
  - intros n f.
    now induction f.
Qed.

Definition one_point_theory
  : algebraic_theory
  := make_algebraic_theory _ one_point_is_theory.

(** * 2. The only algebra of the one point theory is the unit type *)

Lemma one_point_theory_algebra_is_trivial
  : ∏ (A : algebra one_point_theory), A ≃ unit.
Proof.
  intro A.
  apply weqcontrtounit.
  use tpair.
  - use (action (tt : (one_point_theory 0 : hSet)) (weqvecfun 0 vnil)).
  - intro a.
    rewrite <- (var_action _ (make_stn 1 0 (idpath _)) (λ _, a)
      : _ = a).
    exact (lift_constant_action _ _ _).
Qed.
