(**************************************************************************************************

  λ-theories

  A λ-theory is a model for the untyped λ-calculus. It is a structure with variables, substitution,
  abstraction and application. Here it is formalized as an algebraic theory L, with functions
  between the L n and L (S n) that are compatible with the substitution in some way.
  This file defines what a λ-theory is and gives accessors, constructors and defines what it means
  for a λ-theory to have β- and η-equality.

  Contents
  1. The definition of λ-theories [lambda_theory]
  2. The definition of β-equality [has_beta]
  3. The definiiton of η-equality [has_eta]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Local Open Scope algebraic_theories.

(** * 1. The definition of λ-theories *)

Definition lambda_theory_data : UU
  := lambda_theory_data_cat.

Definition make_lambda_theory_data
  (T : algebraic_theory)
  (abs : ∏ n, T n → T (S n))
  (app : ∏ n, T (S n) → T n)
  : lambda_theory_data
  := T ,, abs ,, app.

Coercion lambda_theory_data_to_algebraic_theory (L : lambda_theory_data)
  : algebraic_theory
  := pr1 L.

Definition app {L : lambda_theory_data} {n : nat} : L n → L (S n) := pr12 L n.

Definition abs {L : lambda_theory_data} {n : nat} : L (S n) → L n := pr22 L n.

Definition lambda_theory : UU := lambda_theory_cat.

Definition make_is_lambda_theory
  {L : lambda_theory_data}
  (app_comp : app_comp_ax L)
  (abs_comp : abs_comp_ax L)
  : is_lambda_theory L
  := app_comp ,, abs_comp.

Definition make_lambda_theory
  (L : lambda_theory_data)
  (H : is_lambda_theory L)
  : lambda_theory
  := L ,, H.

Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data := pr1 L.

Definition app_comp
  (L : lambda_theory)
  {m n : nat}
  (f : L m)
  (g : stn m → L n)
  : app (f • g) = extended_composition (app f) g
  := pr12 L m n f g.

Definition abs_comp
  (L : lambda_theory)
  {m n : nat}
  (f : L (S m))
  (g : stn m → L n)
  : abs (extended_composition f g) = (abs f) • g
  := pr22 L m n f g.

(** * 2. The definition of β-equality *)

Definition has_beta (L : lambda_theory) : UU
  := ∏ n (l : L (S n)), app (abs l) = l.

(** * 3. The definiiton of η-equality *)

Definition has_eta (L : lambda_theory) : UU
  := ∏ n (l : L n), abs (app l) = l.
