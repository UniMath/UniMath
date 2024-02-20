(*******************************************************************************************

 Notations for comprehension categories

 We define a bunch of notations and nicer accessors for comprehension categories and their
 functors.

 Contents
 1. Notations and accessors for comprehension categories
 2. Notations and accessors for functors of comprehension categories

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
