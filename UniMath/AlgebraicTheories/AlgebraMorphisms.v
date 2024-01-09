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
Require Import UniMath.AlgebraicTheories.AlgebraCategory.

Local Open Scope cat.

(** * 1. The definition of algebra morphisms *)
(** *** 1.1.2. The property of the morphisms *)

Definition algebra_morphism
  {T : algebraic_theory}
  (A A' : algebra T)
  : UU
  := algebra_cat T⟦A, A'⟧.

Definition mor_action_ax
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : A → A')
  : UU
  := ∏ n (f : T n) a, F (action f a) = action f (λ i, F (a i)).

Definition algebra_morphism_to_function
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : algebra_morphism A A')
  : A → A'
  := pr1 F.

Coercion algebra_morphism_to_function :
  algebra_morphism >-> Funclass.

Definition make_algebra_morphism
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : A → A')
  (H : mor_action_ax F)
  : algebra_morphism A A'
  := F ,, H ,, tt.

Definition mor_action
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : algebra_morphism A A')
  {n : nat}
  (f : T n)
  (a : stn n → A)
  : F (action f a) = action f (λ i, F (a i))
  := pr12 F n f a.

Lemma isaprop_preserves_action
  {T : algebraic_theory}
  {A A' : algebra T}
  (F : A → A')
  : isaprop (mor_action_ax F).
Proof.
  repeat (apply impred_isaprop; intro).
  apply setproperty.
Qed.

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
    - apply isaprop_preserves_action.
    - apply isapropunit.
  }
  exact H.
Qed.
