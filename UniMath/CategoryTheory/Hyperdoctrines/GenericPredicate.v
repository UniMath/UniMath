(**********************************************************************************************

 Generic predicates in triposes

 We show that every tripos has a generic predicate (Theorem 4.4 in "Tripos Theory in Retrospect"
 by Andrew Pitts). In essence, a generic predicate is a formula from which all other formulas
 can be constructed. More concretely, a generic predicate in a tripos consists of
 - a type `Ω`;
 - a formula `prf` on `Ω`;
 - for every formula `φ` in some context `Γ` a substitution `f` from `Γ` to `Ω` such that `φ`
   is equal to `prf [ t ]`.
 Every term `t` of type `Ω` in context `Γ` thus gives rise to a formula in context `Γ`, namely
 `prf [ t ]`. In addition, every formula `φ` in context ‵Γ` is equal to `prf [ f ]` for some
 substitution `f` from `Γ` to `Ω`. Hence, we have a surjection from terms of type `Ω` in context
 `Γ` to formulas in context `Γ`.

 The generic predicate is used in the tripos to topos construction to construct the subobject
 classifier of the topos. Note that a first-order hyperdoctrine with generic predicate does not
 necessarily give rise to a tripos. This would be the case if we assume the category of types to
 be Cartesian closed.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Definition of generic predicates in first-order hyperdoctrines
 2. Construction of generic predicates in triposes

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
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. Definition of generic predicates in first-order hyperdoctrines *)
Definition is_generic_predicate
           {H : first_order_hyperdoctrine}
           (Ω : ty H)
           (prf : form Ω)
  : UU
  := ∏ (Γ : ty H)
       (φ : form Γ),
     ∑ (f : tm Γ Ω),
     φ = prf [ f ].

Definition generic_predicate
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (Ω : ty H)
       (prf : form Ω),
     is_generic_predicate Ω prf.

Definition make_generic_predicate
           {H : first_order_hyperdoctrine}
           (Ω : ty H)
           (prf : form Ω)
           (HΩ : is_generic_predicate Ω prf)
  : generic_predicate H
  := Ω ,, prf ,, HΩ.

Coercion ty_of_generic_predicate
         {H : first_order_hyperdoctrine}
         (Ω : generic_predicate H)
  : ty H.
Proof.
  exact (pr1 Ω).
Defined.

Definition prf_of_generic_predicate
           {H : first_order_hyperdoctrine}
           (Ω : generic_predicate H)
  : form Ω
  := pr12 Ω.

Definition mor_to_generic_predicate
           {H : first_order_hyperdoctrine}
           (Ω : generic_predicate H)
           {Γ : ty H}
           (φ : form Γ)
  : tm Γ Ω
  := pr1 (pr22 Ω Γ φ).

Proposition mor_to_generic_predicate_eq
            {H : first_order_hyperdoctrine}
            (Ω : generic_predicate H)
            {Γ : ty H}
            (φ : form Γ)
  : φ
    =
    (prf_of_generic_predicate Ω) [ mor_to_generic_predicate Ω φ ].
Proof.
  exact (pr2 (pr22 Ω Γ φ)).
Qed.

(** 2. Construction of generic predicates in triposes *)
Definition tripos_generic_predicate
           (H : tripos)
  : generic_predicate H.
Proof.
  use make_generic_predicate.
  - exact (ℙ 𝟙).
  - exact (let P := tm_var (ℙ 𝟙) in
           !! ∈ P).
  - intros Γ A.
    simple refine (_ ,, _).
    + exact {{ A [ π₂ (tm_var _) ] }}.
    + abstract
        (cbn ;
         rewrite tripos_in_subst ;
         simplify ;
         pose (maponpaths
                 (λ φ, φ [ ⟨ !! , tm_var _ ⟩ ])
                 (mor_to_tripos_power_eq 𝟙 Γ (A [ π₂ (tm_var _) ])))
           as p ;
         cbn in p ;
         rewrite !hyperdoctrine_comp_subst in p ;
         rewrite hyperdoctrine_pr2_subst in p ;
         rewrite var_tm_subst in p ;
         rewrite hyperdoctrine_pair_pr2 in p ;
         rewrite hyperdoctrine_id_subst in p ;
         refine (p @ _) ; clear p ;
         use hyperdoctrine_formula_eq ;
         simplify ;
         apply hyperdoctrine_hyp).
Defined.

Notation "'Ω'" := (ty_of_generic_predicate (tripos_generic_predicate _)).
Notation "'Prf'" := (prf_of_generic_predicate (tripos_generic_predicate _)).

Definition tripos_form_to_tm
           {H : tripos}
           {Γ : ty H}
           (φ : form Γ)
  : tm Γ Ω
  := mor_to_generic_predicate _ φ.

Proposition tripos_form_to_tm_Prf
            {H : tripos}
            {Γ : ty H}
            (φ : form Γ)
  : Prf [ tripos_form_to_tm φ ] = φ.
Proof.
  exact (!(mor_to_generic_predicate_eq (tripos_generic_predicate H) φ)).
Qed.

(**
   This way the construction of the generic predicate in a tripos does not get unfolded.
 *)
#[global] Opaque ty_of_generic_predicate.
#[global] Opaque prf_of_generic_predicate.
#[global] Opaque mor_to_generic_predicate.
