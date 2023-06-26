(* Defines morphisms of algebraic theory algebras. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.

Require Import UniMath.AlgebraicTheories.Tactics.

Definition preserves_action
  {T : algebraic_theory_data}
  {A A' : algebraic_theory_algebra_data T}
  (F : A → A')
  : UU
  := ∏ n f (a : stn n → A), F (action f a) = action f (λ i, F (a i)).

Definition algebraic_theory_algebra_morphism
  {T : algebraic_theory_data}
  (A A' : algebraic_theory_algebra_data T)
  : UU
  := ∑ (F : A → A') (H : preserves_action F), unit.

Definition algebraic_theory_algebra_morphism_to_function
  {T : algebraic_theory_data}
  {A A' : algebraic_theory_algebra_data T}
  (F : algebraic_theory_algebra_morphism A A')
  : A → A'
  := pr1 F.

Coercion algebraic_theory_algebra_morphism_to_function :
  algebraic_theory_algebra_morphism >-> Funclass.

Definition algebraic_theory_algebra_morphism_preserves_action
  {T : algebraic_theory_data}
  {A A' : algebraic_theory_algebra_data T}
  (F : algebraic_theory_algebra_morphism A A')
  : preserves_action F
  := pr12 F.

Lemma isaprop_preserves_action
  {T : algebraic_theory_data}
  {A A' : algebraic_theory_algebra_data T}
  (F : A → A')
  : isaprop (preserves_action F).
Proof.
  prove_hlevel 1.
Qed.
