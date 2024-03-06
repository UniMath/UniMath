(*******************************************************************************************

 Notations for comprehension categories

 We define a bunch of notations and nicer accessors for comprehension categories and their
 functors. We also define terms (i.e., sections of projections), and we define several
 operations of terms.

 Contents
 1. Notations and accessors for comprehension categories
 2. Notations and accessors for functors of comprehension categories
 3. Terms in comprehension categories

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

Declare Scope comp_cat.
Local Open Scope comp_cat.

(** * 1. Notations for comprehension categories *)
Notation "'[]'" := (empty_context _) : comp_cat.

Definition comp_cat_ty
           {C : comp_cat}
           (Γ : C)
  : UU
  := disp_cat_of_types C Γ.

Notation "'ty'" := comp_cat_ty.

Definition comp_cat_ext
           {C : comp_cat}
           (Γ : C)
           (A : ty Γ)
  : C
  := comprehension_functor_ob (comp_cat_comprehension C) A.

Notation "Γ '&' A" := (comp_cat_ext Γ A) (at level 20) : comp_cat.

Definition comp_cat_proj
           {C : comp_cat}
           (Γ : C)
           (A : ty Γ)
  : Γ & A --> Γ
  := comprehension_functor_cod_mor (comp_cat_comprehension C) A.

Notation "'π'" := (comp_cat_proj _) : comp_cat.

Definition comp_cat_comp_mor
           {C : comp_cat}
           {Γ : C}
           {A B : ty Γ}
           (s : A -->[ identity _ ] B)
  : Γ & A --> Γ & B
  := comprehension_functor_mor (comp_cat_comprehension C) s.

Definition comp_cat_comp_z_iso
           {C : comp_cat}
           {Γ : C}
           {A B : ty Γ}
           (s : z_iso_disp (identity_z_iso _) A B)
  : z_iso (Γ & A) (Γ & B)
  := from_z_iso_disp_codomain
       (disp_functor_on_z_iso_disp (comp_cat_comprehension C) s).

Definition subst_ty
           {C : comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : ty Δ)
  : ty Γ
  := cleaving_ob (cleaving_of_types C) s A.

Notation "A '[[' s ']]'" := (subst_ty s A) (at level 20) : comp_cat.

Definition comp_cat_subst
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : A[[ s ]] -->[ s ] A
  := mor_disp_of_cartesian_lift _ _ (cleaving_of_types C Γ₁ Γ₂ s A).

Definition comp_cat_iso_subst
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : z_iso Γ₂ Γ₁)
  : z_iso_disp s (A[[ s ]]) A.
Proof.
  use make_z_iso_disp.
  - exact (mor_disp_of_cartesian_lift _ _ (cleaving_of_types C Γ₁ Γ₂ s A)).
  - use is_z_iso_from_is_cartesian.
    apply cartesian_lift_is_cartesian.
Defined.

Definition comp_cat_extend_over
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : Γ₂ & (A [[ s ]]) --> Γ₁ & A
  := comprehension_functor_mor (comp_cat_comprehension C) (comp_cat_subst A s).

Definition comp_cat_extend_over_iso
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : Γ₂ --> Γ₁)
           (Hs : is_z_isomorphism s)
  : z_iso (Γ₂ & (A [[ s ]])) (Γ₁ & A)
  := from_z_iso_disp_codomain
       (disp_functor_on_z_iso_disp
          (comp_cat_comprehension C)
          (comp_cat_iso_subst A (s ,, Hs))).

Definition comp_cat_is_pullback
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : @isPullback
       C
       _ _ _ _
       (π A)
       s
       (comprehension_functor_mor
          (comp_cat_comprehension C)
          (cleaving_of_types C _ _ s A))
       (π (A [[ s ]]))
       (comprehension_functor_mor_comm
          (comp_cat_comprehension C)
          (cleaving_of_types C _ _ s A))
  := cartesian_isPullback_in_cod_disp
       _
       (cartesian_disp_functor_on_cartesian
          (comp_cat_comprehension C)
          (cleaving_of_types C _ _ s A)).

Definition comp_cat_pullback
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (A : ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : Pullback (π A) s
  := make_Pullback _ (comp_cat_is_pullback A s).

Definition cartesian_to_is_pullback
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           {s : Γ₁ --> Γ₂}
           {A₁ : ty Γ₁}
           {A₂ : ty Γ₂}
           (t : A₁ -->[ s ] A₂)
           (Ht : is_cartesian t)
  : isPullback (comprehension_functor_mor_comm (comp_cat_comprehension C) t)
  := cartesian_isPullback_in_cod_disp
       _
       (cartesian_disp_functor_on_cartesian (comp_cat_comprehension C) Ht).

Definition cartesian_to_pullback
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           {s : Γ₁ --> Γ₂}
           {A₁ : ty Γ₁}
           {A₂ : ty Γ₂}
           (t : A₁ -->[ s ] A₂)
           (Ht : is_cartesian t)
  : Pullback (π A₂) s
  := make_Pullback _ (cartesian_to_is_pullback t Ht).

Proposition comprehension_functor_mor_factorisation_pr1
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ : C}
            {s₁ : Γ₁ --> Γ₂}
            {s₂ : Γ₂ --> Γ₃}
            {A₁ : ty Γ₁}
            {A₂ : ty Γ₂}
            {A₃ : ty Γ₃}
            (t : A₂ -->[ s₂ ] A₃)
            (Ht : is_cartesian t)
            (t' : A₁ -->[ s₁ · s₂ ] A₃)
  : comprehension_functor_mor
      (comp_cat_comprehension C)
      (cartesian_factorisation Ht _ t')
    · PullbackPr1 (cartesian_to_pullback t Ht)
    =
    comprehension_functor_mor (comp_cat_comprehension C) t'.
Proof.
  cbn.
  refine (!(comprehension_functor_mor_comp _ _ _) @ _).
  apply maponpaths.
  apply cartesian_factorisation_commutes.
Qed.

Proposition comprehension_functor_mor_factorisation_pr2
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ : C}
            {s₁ : Γ₁ --> Γ₂}
            {s₂ : Γ₂ --> Γ₃}
            {A₁ : ty Γ₁}
            {A₂ : ty Γ₂}
            {A₃ : ty Γ₃}
            (t : A₂ -->[ s₂ ] A₃)
            (Ht : is_cartesian t)
            (t' : A₁ -->[ s₁ · s₂ ] A₃)
  : comprehension_functor_mor
      (comp_cat_comprehension C)
      (cartesian_factorisation Ht _ t')
    · π _
    =
    π _ · s₁.
Proof.
  rewrite comprehension_functor_mor_comm.
  apply idpath.
Qed.

(** * 2. Notations and accessors for functors of comprehension categories *)
Definition comp_cat_functor_empty_context_isTerminal
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
  : isTerminal _ (F [])
  := comp_cat_functor_terminal F _ (pr2 []).

Definition comp_cat_functor_empty_context
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
  : Terminal C₂.
Proof.
  use make_Terminal.
  - exact (F []).
  - exact (comp_cat_functor_empty_context_isTerminal F).
Defined.

Definition comp_cat_functor_empty_context_arrow
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           (Γ : C₂)
  : Γ --> F []
  := TerminalArrow (comp_cat_functor_empty_context F) Γ.

Proposition comp_cat_functor_empty_context_arrow_eq
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ : C₂}
            (f g : Γ --> F [])
  : f = g.
Proof.
  exact (TerminalArrowEq (T := comp_cat_functor_empty_context F) f g).
Qed.

Definition comp_cat_functor_empty_context_is_z_iso
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
  : is_z_isomorphism (TerminalArrow [] (F [])).
Proof.
  use make_is_z_isomorphism.
  - exact (comp_cat_functor_empty_context_arrow F []).
  - split.
    + use comp_cat_functor_empty_context_arrow_eq.
    + use TerminalArrowEq.
Defined.

Definition comp_cat_functor_extension
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (Γ : C₁)
           (A : ty Γ)
  : z_iso (F(Γ & A)) (F Γ & comp_cat_type_functor F Γ A).
Proof.
  refine (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) A ,, _).
  apply (full_comp_cat_functor_is_z_iso F).
Defined.

Definition comp_cat_functor_extension_mor
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ : C₁}
           {A₁ A₂ : ty Γ}
           (f : A₁ -->[ identity _ ] A₂)
  : F Γ & comp_cat_type_functor F Γ A₁ --> F Γ & comp_cat_type_functor F Γ A₂
  := comprehension_functor_mor
       (comp_cat_comprehension C₂)
       ((♯ (comp_cat_type_functor F) f)%mor_disp).

(** * 3. Terms in comprehension categories *)
Definition comp_cat_tm
           {C : comp_cat}
           (Γ : C)
           (A : ty Γ)
  : UU
  := ∑ (t : Γ --> Γ & A), t · π A = identity Γ.

Definition make_comp_cat_tm
           {C : comp_cat}
           {Γ : C}
           {A : ty Γ}
           (t : Γ --> Γ & A)
           (p : t · π A = identity Γ)
  : comp_cat_tm Γ A
  := t ,, p.

Coercion comp_cat_tm_to_mor
         {C : comp_cat}
         {Γ : C}
         {A : ty Γ}
         (t : comp_cat_tm Γ A)
  : Γ --> Γ & A.
Proof.
  exact (pr1 t).
Defined.

Proposition comp_cat_tm_eq
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            (t : comp_cat_tm Γ A)
  : t · π A = identity Γ.
Proof.
  exact (pr2 t).
Qed.

Proposition eq_comp_cat_tm
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            {t₁ t₂ : comp_cat_tm Γ A}
            (p : comp_cat_tm_to_mor t₁ = comp_cat_tm_to_mor t₂)
  : t₁ = t₂.
Proof.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  exact p.
Qed.

Definition sub_to_extension
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (s : Δ --> Γ)
           (t : comp_cat_tm Δ (A [[ s ]]))
  : Δ --> Γ & A
  := t · PullbackPr1 (comp_cat_pullback A s).

Definition sub_to_extension_tm
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (s : Δ --> Γ & A)
  : comp_cat_tm Δ (A [[ s · π _ ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback _ _)).
    + exact s.
    + apply identity.
    + abstract
        (rewrite id_left ;
         apply idpath).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
Defined.

Definition transport_term_sub_eq
           {C : comp_cat}
           {Γ Δ : C}
           {s₁ s₂ : Δ --> Γ}
           (p : s₁ = s₂)
           {A : ty Γ}
           (t : comp_cat_tm Δ (A [[ s₁ ]]))
  : comp_cat_tm Δ (A [[ s₂ ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback _ _)).
    + exact (t · comp_cat_extend_over _ _).
    + apply identity.
    + abstract
        (induction p ;
         rewrite id_left ;
         rewrite !assoc' ;
         unfold comp_cat_extend_over ;
         refine (maponpaths (λ z, _ · z) (comprehension_functor_mor_comm _ _) @ _) ;
         rewrite !assoc ;
         refine (maponpaths (λ z, z · _) (comp_cat_tm_eq t) @ _) ;
         apply id_left).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
Defined.

Proposition eq_sub_to_extension
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            {s₁ s₂ : Δ --> Γ & A}
            (p : s₁ · π _ = s₂ · π _)
            (q : transport_term_sub_eq p (sub_to_extension_tm s₁)
                 =
                 sub_to_extension_tm s₂)
  : s₁ = s₂.
Proof.
  pose (maponpaths (λ z, pr1 z · PullbackPr1 (comp_cat_pullback _ _)) q) as q'.
  simpl in q'.
  rewrite !PullbackArrow_PullbackPr1 in q'.
  refine (_ @ q').
  enough (s₁ = sub_to_extension_tm s₁ · comp_cat_extend_over A (s₁ · π A)) as H.
  {
    exact H.
  }
  clear p q q' s₂.
  refine (!_).
  apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A (s₁ · π A))).
Qed.

Definition sub_comp_cat_tm
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (t : comp_cat_tm Γ A)
           (s : Δ --> Γ)
  : comp_cat_tm Δ (A [[ s ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback A s)).
    + exact (s · t).
    + apply identity.
    + abstract
        (rewrite id_left ;
         rewrite !assoc' ;
         rewrite comp_cat_tm_eq ;
         apply id_right).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A s))).
Defined.

Proposition sub_comp_cat_tm_pr1
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (t : comp_cat_tm Γ A)
            (s : Δ --> Γ)
  : sub_comp_cat_tm t s · PullbackPr1 (comp_cat_pullback A s) = s · t.
Proof.
  apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A s)).
Qed.

Proposition sub_comp_cat_tm_pr2
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (t : comp_cat_tm Γ A)
            (s : Δ --> Γ)
  : sub_comp_cat_tm t s · π _ = identity _.
Proof.
  apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A s)).
Qed.
