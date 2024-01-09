(**************************************************************************************************

  λ-theory morphisms

  Defines what a morphism of λ-theories is.

  Contents
  1. The definition of λ-theory morphisms [lambda_theory_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope algebraic_theories.
Local Open Scope cat.

(** * 1. The definition of λ-theory morphisms [lambda_theory_morphism] *)

Definition lambda_theory_morphism
  (L L' : lambda_theory)
  : UU
  := lambda_theory_cat⟦L, L'⟧.

Definition make_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : algebraic_theory_morphism L L')
  (Happ : mor_app_ax F)
  (Habs : mor_abs_ax F)
  : lambda_theory_morphism L L'
  := (F ,, Happ ,, Habs) ,, tt.

Coercion lambda_theory_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  : algebraic_theory_morphism L L'
  := pr11 F.

Definition mor_app
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  {n : nat}
  (f : L n)
  : F _ (app f) = app (F _ f)
  := pr121 F n f.

Definition mor_abs
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  {n : nat}
  (f : L (S n))
  : F _ (abs f) = abs (F _ f)
  := pr221 F n f.
