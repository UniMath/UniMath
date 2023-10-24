(**************************************************************************************************

  λ-theory morphisms

  Defines what a morphism of λ-theories is.

  Contents
  1. The definition of λ-theory morphisms [lambda_theory_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope algebraic_theories.

(** * 1. The definition of λ-theory morphisms [lambda_theory_morphism] *)

Definition lambda_theory_data_morphism
  (L L' : lambda_theory_data)
  : UU
  := ∑ (F : algebraic_theory_morphism L L'),
      (∏ n t, F _ (app t) = app (F n t)) ×
      (∏ n t, F _ (abs t) = abs (F (S n) t)).

Definition make_lambda_theory_data_morphism
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  (Happ : ∏ n t, F _ (app t) = app (F n t))
  (Habs : ∏ n t, F _ (abs t) = abs (F (S n) t))
  : lambda_theory_data_morphism L L'
  := F ,, Happ ,, Habs.

Coercion lambda_theory_data_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  : algebraic_theory_morphism L L'
  := pr1 F.

Definition lambda_theory_data_morphism_preserves_app
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  (n : nat) (t : (L n : hSet))
  : F _ (app t) = app (F _ t)
  := pr12 F n t.

Definition lambda_theory_data_morphism_preserves_abs
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  (n : nat) (t : (L (S n) : hSet))
  : F _ (abs t) = abs (F _ t)
  := pr22 F n t.
Definition lambda_theory_morphism
  (L L' : lambda_theory)
  : UU
  := lambda_theory_data_morphism L L' × unit.

Definition make_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : lambda_theory_data_morphism L L')
  : lambda_theory_morphism L L'
  := F ,, tt.

Coercion lambda_theory_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  : algebraic_theory_morphism L L'
  := pr1 F.
