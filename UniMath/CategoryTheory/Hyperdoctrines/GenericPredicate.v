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

 We look at both generic predicates and weak generic predicates. The difference between them
 is that weak generic predicates are formulated using an axiom. Specifically, every formula
 gives rise to a term of type `Ω` if we have a generic predicate, and this assignment gives
 us an actual operation on formulas. For weak generic predicate,s we use the existential
 quantifier instead.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Definition of generic predicates in first-order hyperdoctrines
 2. Construction of generic predicates in triposes
 3. Construction of power objects from generic predicates
 4. Definition of weak generic predicates in first-order hyperdoctrines
 5. Construction of weak generic predicates in weak triposes

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
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Exponentials.


Local Open Scope cat.
Local Open Scope hd.
Local Open Scope tripos.

(** * 1. Definition of generic predicates in first-order hyperdoctrines *)
Definition is_generic_predicate
           {H : first_order_hyperdoctrine}
           (X : ty H)
           (prf : form X)
  : UU
  := ∏ (Γ : ty H)
       (φ : form Γ),
     ∑ (f : tm Γ X),
     φ = prf [ f ].

Definition generic_predicate
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (X : ty H)
       (prf : form X),
     is_generic_predicate X prf.

Definition make_generic_predicate
           {H : first_order_hyperdoctrine}
           (X : ty H)
           (prf : form X)
           (HΩ : is_generic_predicate X prf)
  : generic_predicate H
  := X ,, prf ,, HΩ.

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

Notation "'Ω'" := (ty_of_generic_predicate (tripos_generic_predicate _)) : tripos.
Notation "'Prf'" := (prf_of_generic_predicate (tripos_generic_predicate _)) : tripos.

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

(** * 3. Construction of power objects from generic predicates *)
Definition is_tripos_from_generic_predicate
           {H : first_order_hyperdoctrine}
           (ΩP : generic_predicate H)
           (E : Exponentials (hyperdoctrine_binproducts H))
  : is_tripos H.
Proof.
  intros X.
  simple refine (_ ,, _ ,, _).
  - exact (exp (E X) (ΩP : ty H)).
  - exact ((prf_of_generic_predicate ΩP) [ exp_eval (E X) (ΩP : ty H) ]).
  - intros Γ R.
    simple refine (_ ,, _).
    + exact (exp_lam (E X) (mor_to_generic_predicate ΩP R)).
    + abstract
        (cbn ;
         rewrite (mor_to_generic_predicate_eq ΩP R) ;
         hypersimplify ;
         apply maponpaths ;
         unfold tm_subst, hyperdoctrine_pair ;
         unfold tm_var, hyperdoctrine_pr1, hyperdoctrine_pr2 ;
         cbn ;
         rewrite !id_left ;
         refine (!(exp_beta (E X) (mor_to_generic_predicate ΩP R)) @ _) ;
         apply maponpaths_2 ;
         unfold BinProductOfArrows ;
         rewrite id_right ;
         do 4 apply maponpaths ;
         apply mor_to_generic_predicate_eq).
Defined.

Definition tripos_from_generic_predicate
           {H : first_order_hyperdoctrine}
           (ΩP : generic_predicate H)
           (E : Exponentials (hyperdoctrine_binproducts H))
  : tripos
  := H ,, is_tripos_from_generic_predicate ΩP E.

Close Scope tripos.
Local Open Scope weak_tripos.

(** * 4. Definition of weak generic predicates in first-order hyperdoctrines *)
Definition is_weak_generic_predicate
           {H : first_order_hyperdoctrine}
           (X : ty H)
           (prf : form X)
  : UU
  := ∏ (Γ : ty H)
       (φ : form Γ),
     ⊤ ⊢ (∃h (φ [ π₁ (tm_var _) ] ⇔ prf [ π₂ (tm_var _) ])).

Definition weak_generic_predicate
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (X : ty H)
       (prf : form X),
     is_weak_generic_predicate X prf.

Definition make_weak_generic_predicate
           {H : first_order_hyperdoctrine}
           (X : ty H)
           (prf : form X)
           (HΩ : is_weak_generic_predicate X prf)
  : weak_generic_predicate H
  := X ,, prf ,, HΩ.

Coercion ty_of_weak_generic_predicate
         {H : first_order_hyperdoctrine}
         (X : weak_generic_predicate H)
  : ty H.
Proof.
  exact (pr1 X).
Defined.

Definition prf_of_weak_generic_predicate
           {H : first_order_hyperdoctrine}
           (X : weak_generic_predicate H)
  : form X
  := pr12 X.

Proposition mor_to_weak_generic_predicate
            {H : first_order_hyperdoctrine}
            (X : weak_generic_predicate H)
            {Γ : ty H}
            (φ : form Γ)
  : ⊤ ⊢ (∃h (φ [ π₁ (tm_var _) ] ⇔ (prf_of_weak_generic_predicate X) [ π₂ (tm_var _) ])).
Proof.
  exact (pr22 X Γ φ).
Defined.

(** 5. Construction of weak generic predicates in weak triposes *)
Definition weak_tripos_generic_predicate
           (H : weak_tripos)
  : weak_generic_predicate H.
Proof.
  use make_weak_generic_predicate.
  - exact (ℙ 𝟙).
  - exact (let P := tm_var (ℙ 𝟙) in
           !! ∈ P).
  - abstract
      (intros Γ A ;
       refine (exists_elim
                 (weak_tripos_compr (A [ π₂ (tm_var (𝟙 ×h Γ)) ]) ⊤ (tm_var _))
                 _) ;
       cbn ;
       use weaken_right ;
       hypersimplify_form ;
       use exists_intro ; [ exact (π₂ (tm_var _)) | ] ;
       hypersimplify ;
       unfold weak_tripos_rel_equiv ;
       hypersimplify ;
       refine (hyperdoctrine_cut
                 (forall_elim (hyperdoctrine_hyp _) !!)
                 _) ;
       hypersimplify ;
       use iff_sym ;
       apply hyperdoctrine_hyp).
Defined.

Notation "'Ω'" := (ty_of_weak_generic_predicate (weak_tripos_generic_predicate _))
    : weak_tripos.
Notation "'Prf'" := (prf_of_weak_generic_predicate (weak_tripos_generic_predicate _))
    : weak_tripos.

Definition weak_tripos_form_to_tm
           {H : weak_tripos}
           {Γ X : ty H}
           (φ : form X)
           (Δ : form Γ)
           (x : tm Γ X)
  : Δ ⊢ (∃h (φ [ x [ π₁ (tm_var _) ]tm ] ⇔ Prf [ π₂ (tm_var _) ])).
Proof.
  refine (hyperdoctrine_cut _ _).
  {
    apply truth_intro.
  }
  refine (hyperdoctrine_cut _ _).
  {
    exact (mor_to_weak_generic_predicate
             (weak_tripos_generic_predicate H)
             (φ [ x ])).
  }
  refine (exists_elim _ _).
  {
    use hyperdoctrine_hyp.
  }
  use weaken_right.
  hypersimplify_form.
  use exists_intro.
  {
    exact (π₂ (tm_var _)).
  }
  hypersimplify.
  apply hyperdoctrine_hyp.
Qed.

(**
   This way the construction of the generic predicate in a tripos does not get unfolded.
 *)
#[global] Opaque ty_of_weak_generic_predicate.
#[global] Opaque prf_of_weak_generic_predicate.
#[global] Opaque mor_to_weak_generic_predicate.
