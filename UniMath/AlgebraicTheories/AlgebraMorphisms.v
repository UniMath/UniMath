(**************************************************************************************************

  Algebra morphisms

  Defines what a morphism of algebras is.

  Contents
  1. The definition of algebra morphisms [algebra_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.

(** * 1. The definition of algebra morphisms *)

Definition preserves_action
  {T : algebraic_theory_data}
  {A A' : algebra_data T}
  (F : A → A')
  : UU
  := ∏ (n : nat) (f : (T n : hSet)) (a : stn n → A), F (action f a) = action f (λ i, F (a i)).

Definition algebra_morphism
  {T : algebraic_theory_data}
  (A A' : algebra_data T)
  : UU
  := ∑ (F : A → A') (H : preserves_action F), unit.

Definition algebra_morphism_to_function
  {T : algebraic_theory_data}
  {A A' : algebra_data T}
  (F : algebra_morphism A A')
  : A → A'
  := pr1 F.

Coercion algebra_morphism_to_function :
  algebra_morphism >-> Funclass.

Definition algebra_morphism_preserves_action
  {T : algebraic_theory_data}
  {A A' : algebra_data T}
  (F : algebra_morphism A A')
  : preserves_action F
  := pr12 F.

Lemma isaprop_preserves_action
  {T : algebraic_theory_data}
  {A A' : algebra_data T}
  (F : A → A')
  : isaprop (preserves_action F).
Proof.
  repeat (apply impred_isaprop; intro).
  apply setproperty.
Qed.
