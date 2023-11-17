(**************************************************************************************************

  The projections theory

  This algebraic theory is the free theory on the empty set. Therefore, it is also the initial
  algebraic theory. The set T(n) just consists of the n variables.
  This theory is called the "projections theory" because Hyland calls variables "projections". When
  interpreting an algebraic theory as the endomorphism theory (the theory consisting of the
  morphisms X^n -> X for some object X in some category), the variables are exactly the projections.

  Contents
  1. The definition of the projections theory [projections_theory]
  2. The definition of a T-algebra structure on every set [projections_theory_algebra]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.Algebras.

(** * 1. The definition of the projections theory *)

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

(** * 2. The definition of a T-algebra structure on every set *)

Definition projections_theory_algebra_data (A : hSet)
  : algebra_data projections_theory
  := make_algebra_data A (λ n (i : (projections_theory n : hSet)) f, f i).

Lemma projections_theory_algebra_is_algebra (A : hSet)
  : is_algebra (projections_theory_algebra_data A).
Proof.
  now use make_is_algebra;
    repeat intro.
Qed.

Definition projections_theory_algebra (A : hSet)
  : algebra projections_theory
  := make_algebra _ (projections_theory_algebra_is_algebra A).
