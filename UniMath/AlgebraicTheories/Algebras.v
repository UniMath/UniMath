(**************************************************************************************************

  Algebras

  Defines what an algebra for an algebraic theory is, and gives constructors, accessors and
  some properties.

  Contents
  1. The definition of algebras [algebra]
  2. An equality lemma [algebra_eq]
  3. Some properties of algebras

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraCategory.

Local Open Scope algebraic_theories.

(** * 1. The definition of algebras *)

Definition algebra_data
  (T : algebraic_theory)
  : UU
  := ∑ (A : hSet), ∏ n f a, action_ax T A n f a.

Definition make_algebra_data
  {T : algebraic_theory}
  (A : hSet)
  (action : ∏ n f a, action_ax T A n f a)
  : algebra_data T
  := A ,, action.

Coercion algebra_data_to_hset
  {T : algebraic_theory}
  (A : algebra_data T)
  : hSet
  := pr1 A.

Definition action
  {T : algebraic_theory}
  {A : algebra_data T}
  {n : nat}
  (f : T n)
  (a : stn n → A)
  : action_ax T A n f a
  := pr2 A n f a.

Definition is_algebra
  {T : algebraic_theory}
  (A : algebra_data T)
  : UU
  := (∏ m n f g a, comp_action_ax T A (@action T A) m n f g a)
    × (∏ n i a, pr_action_ax T A (@action T A) n i a).

Definition make_is_algebra
  {T : algebraic_theory}
  (A : algebra_data T)
  (H1 : ∏ m n f g a, comp_action_ax T A (@action T A) m n f g a)
  (H2 : ∏ n i a, pr_action_ax T A (@action T A) n i a)
  : is_algebra A
  := H1 ,, H2.

Definition algebra
  (T : algebraic_theory)
  : UU
  := algebra_cat T.

Definition make_algebra
  {T : algebraic_theory}
  (A : algebra_data T)
  (H : is_algebra A)
  : algebra T
  := pr1 A ,, pr2 A ,, H.

Coercion algebra_to_algebra_data
  {T : algebraic_theory}
  (A : algebra T)
  : algebra_data T
  := make_algebra_data (pr1 A) (pr12 A).

Definition comp_action
  {T : algebraic_theory}
  (A : algebra T)
  {m n : nat}
  (f : T m)
  (g : stn m → T n)
  (a : stn n → A)
  : comp_action_ax T A (@action T A) m n f g a
  := pr122 A m n f g a.

Definition pr_action
  {T : algebraic_theory}
  (A : algebra T)
  {n : nat}
  (i : stn n)
  (a : stn n → A)
  : pr_action_ax T A (@action T A) n i a
  := pr222 A n i a.

(** * 2. An equality lemma *)

Lemma algebra_eq
  {T : algebraic_theory}
  (A B : algebra T)
  (H1 : (A : hSet) = (B : hSet))
  (H2 : ∏ n f, transportf (λ (X : hSet), (stn n → X) → X) H1 (action f) = action f)
  : A = B.
Proof.
  use total2_paths_f.
  - exact H1.
  - use subtypePath.
    {
      intro.
      apply isaprop_full_is_algebra.
    }
    refine (pr1_transportf H1 _ @ _).
    refine (transportf_sec_constant _ _ @ _).
    apply funextsec.
    intro.
    refine (transportf_sec_constant _ _ @ _).
    apply funextsec.
    intro.
    apply H2.
Qed.

(** * 3. Some properties of algebras *)

Lemma lift_constant_action
  {T : algebraic_theory}
  {A : algebra T}
  (n : nat)
  (f : T 0)
  (a : stn n → A)
  : action (lift_constant n f) a = action f (weqvecfun _ vnil).
Proof.
  refine (comp_action _ _ _ a @ _).
  apply maponpaths, funextfun.
  intro i.
  exact (fromempty (negnatlthn0 _ (stnlt i))).
Qed.
