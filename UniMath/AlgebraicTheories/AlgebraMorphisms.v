(**************************************************************************************************

  Algebra morphisms

  Defines what a morphism of algebras is.

  Contents
  1. The definition of algebra morphisms [algebra_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.

Local Open Scope cat.

(** * 1. The definition of algebra morphisms *)
(** *** 1.1.2. The property of the morphisms *)

Definition algebra_morphism
  {T : algebraic_theory}
  (A A' : algebra T)
  : UU
  := algebra_cat T⟦A, A'⟧.

Definition algebra_morphism_to_function
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : algebra_morphism A A')
  : A → A'
  := pr1 F.

Coercion algebra_morphism_to_function :
  algebra_morphism >-> Funclass.

Definition is_algebra_morphism
  {T : algebraic_theory}
  {A A' : algebra_data T}
  (F : A → A')
  : UU
  := ∏ n f a, mor_action_ax (identity T) F (@action T A) (@action T A') n f a.

Definition make_algebra_morphism
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : A → A')
  (H : is_algebra_morphism F)
  : algebra_morphism A A'
  := F ,, H ,, tt.

Definition mor_action
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : algebra_morphism A A')
  {n : nat}
  (f : T n)
  (a : stn n → A)
  : mor_action_ax (identity T) F (@action T A) (@action T A') n f a
  := pr12 F n f a.

Lemma algebra_morphism_eq
  {T : algebraic_theory}
  {A A' : algebra T}
  (F F' : algebra_morphism A A')
  (H : (F : A → A') = (F' : A → A'))
  : F = F'.
Proof.
  use subtypePath.
  {
    intro.
    use isapropdirprod.
    - repeat (apply impred_isaprop; intro).
      apply setproperty.
    - apply isapropunit.
  }
  exact H.
Qed.

Lemma algebra_mor_comp
  {T : algebraic_theory}
  {A A' A'' : algebra T}
  (F : algebra_morphism A A')
  (F' : algebra_morphism A' A'')
  : algebra_morphism_to_function (F · F') = funcomp F F'.
Proof.
  refine (pr1_transportf (B := λ _, A → A'') _ _ @ _).
  exact (maponpaths (λ z, z _) (transportf_const _ _)).
Qed.
