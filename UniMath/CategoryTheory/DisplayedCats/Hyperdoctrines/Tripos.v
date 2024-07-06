(**********************************************************************************************

 Triposes

 In the literature, various examples of toposes have been established. Among those, are
 1. Realizability toposes, which arise from partial combinatory algebras.
 2. Sets valued in a complete Heyting algebra.
 These examples can be captured in various general frameworks, and one of them is given by
 triposes. In essence, a tripos is a place where one can interpret first-order predicate logic
 and where one has power sets. Concretely, this means that a tripos is given by a first-order
 hyperdoctrine such that for every object `X` there is a powerset object `PX` and a membership
 predicate on `X ×h PX`. There also is some kind of universal property that relates predicates
 on `X` in context `Γ` and terms of type `PX`. This is expressed by the axiom (CA) in the
 paper "Tripos Theory in Retrospect" by Andrew Pitts. This file gives the definition of
 triposes.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Some substitutions necessary to define triposes
 2. The definition of triposes

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.FirstOrderHyperdoctrine.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Some substitutions necessary to define triposes *)
Definition hyperdoctrine_sub_pr_1_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) A
  := π₁ (π₁ (π₁ (identity _))).

Definition hyperdoctrine_sub_pr_2_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) B
  := π₂ (π₁ (π₁ (identity _))).

Definition hyperdoctrine_sub_pr_3_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) C
  := π₂ (π₁ (identity _)).

Definition hyperdoctrine_sub_pr_4_of_4
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) D
  := π₂ (identity _).

Definition hyperdoctrine_sub_pr_4_3
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) (D ×h C)
  := ⟨ hyperdoctrine_sub_pr_4_of_4 , hyperdoctrine_sub_pr_3_of_4 ⟩.

Definition hyperdoctrine_sub_pr_4_2
           {H : first_order_hyperdoctrine}
           {A B C D : ty H}
  : tm (((A ×h B) ×h C) ×h D) (D ×h B)
  := ⟨ hyperdoctrine_sub_pr_4_of_4 , hyperdoctrine_sub_pr_2_of_4 ⟩.

Arguments hyperdoctrine_sub_pr_1_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_2_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_3_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_of_4 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_3 {_ _ _ _ _} /.
Arguments hyperdoctrine_sub_pr_4_2 {_ _ _ _ _} /.

(** * 2. The definition of triposes *)
Definition is_tripos
           (H : first_order_hyperdoctrine)
  : UU
  := ∏ (X : ty H),
     ∑ (PX : ty H)
       (inX : form (X ×h PX)),
     ∏ (Γ : ty H)
       (R : form (X ×h Γ)),
     let s₁ := (hyperdoctrine_sub_pr_4_3 : tm (((𝟙 ×h Γ) ×h PX) ×h X) _) in
     let s₂ := (hyperdoctrine_sub_pr_4_2 : tm (((𝟙 ×h Γ) ×h PX) ×h X) _) in
     ⊤ ⊢ ∀h ∃h ∀h ((inX [ s₁ ] ⇒ R [ s₂ ]) ∧ (R [ s₂ ] ⇒ inX [ s₁ ])).

Definition tripos
  : UU
  := ∑ (H : first_order_hyperdoctrine), is_tripos H.

Coercion tripos_to_first_order_hyperdoctrine
         (H : tripos)
  : first_order_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Definition make_tripos
           (H : first_order_hyperdoctrine)
           (HH : is_tripos H)
  : tripos
  := H ,, HH.
