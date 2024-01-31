From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
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
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope algebraic_theories.
Local Open Scope cat.

(** * 1. The definition of λ-theory morphisms [lambda_theory_morphism] *)

Definition lambda_theory_morphism
  (L L' : lambda_theory)
  : UU
  := lambda_theory_cat⟦L, L'⟧.

Definition is_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : algebraic_theory_morphism L L)
  : UU
  := (∏ n f, mor_app_ax F n f) ×
    (∏ n f, mor_abs_ax F n f).

Definition make_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : algebraic_theory_morphism L L')
  (Happ : ∏ n f, mor_app_ax F n f)
  (Habs : ∏ n f, mor_abs_ax F n f)
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
  : mor_app_ax F n f
  := pr121 F n f.

Definition mor_abs
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  {n : nat}
  (f : L (S n))
  : mor_abs_ax F n f
  := pr221 F n f.

Lemma lambda_theory_morphism_eq
  {L L' : lambda_theory}
  (F F' : lambda_theory_morphism L L')
  (H : (F : algebraic_theory_morphism L L') = F')
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropunit.
  }
  apply subtypePath.
  {
    intro.
    apply isapropdirprod;
      do 2 (apply impred_isaprop; intro);
      apply setproperty.
  }
  apply H.
Qed.
