(*******************************************************************************************

 Notations for comprehension categories

 We define a bunch of notations and nicer accessors for comprehension categories, their
 functors, and natural transformations. We also define terms (i.e., sections of projections),
 and we define several operations of terms.

 In this development we consider the internal language of comprehension categories. We develop
 this in the generality of comprehension categories that are not necessarily full. For this
 reason, we consider coercions between types. In a comprehension category, there is a notion
 of morphism between types, and this notion gives us a (proof relevant) subtyping relation.

 Contents
 1. Notations and accessors for comprehension categories
 2. Terms in comprehension categories
 3. Coercion of terms
 4. Substitution and coherence
 5. Variable rule
 6. Notations and accessors for functors of comprehension categories
 7. Notations and accessors for natural transformations of comprehension categories

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.
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

Definition comp_cat_coercion
           {C : comp_cat}
           {Γ : C}
           (A B : ty Γ)
  : UU
  := fiber_category _ _ ⟦ A , B ⟧.

Notation "A <: B" := (comp_cat_coercion A B) (at level 55).

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

Proposition comp_cat_comp_mor_comm
            {C : comp_cat}
            {Γ : C}
            {A B : ty Γ}
            (s : A <: B)
  : comp_cat_comp_mor s · π B = π A.
Proof.
  refine (comprehension_functor_mor_comm _ s @ _).
  apply id_right.
Qed.

Proposition comp_cat_comp_mor_id
            {C : comp_cat}
            {Γ : C}
            (A : ty Γ)
  : comp_cat_comp_mor (id_disp A) = identity _.
Proof.
  apply comprehension_functor_mor_id.
Qed.

Proposition comp_cat_comp_mor_comp
            {C : comp_cat}
            {Γ : C}
            {A₁ A₂ A₃ : ty Γ}
            (s₁ : A₁ <: A₂)
            (s₂ : A₂ <: A₃)
  : comp_cat_comp_mor (s₁ · s₂)
    =
    comp_cat_comp_mor s₁ · comp_cat_comp_mor s₂.
Proof.
  refine (_ @ comprehension_functor_mor_comp _ s₁ s₂).
  cbn.
  unfold comp_cat_comp_mor, comprehension_functor_mor.
  rewrite disp_functor_transportf, transportf_cod_disp.
  apply idpath.
Qed.

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

Definition subst_ty_iso
           {C : comp_cat}
           {Γ Δ Δ' : C}
           (s : Γ --> Δ)
           {A : ty Δ}
           {B : ty Δ'}
           (f : z_iso Δ Δ')
           (ff : z_iso_disp f A B)
  : z_iso_disp
      (identity_z_iso _)
      (A [[ s ]])
      (B [[ s · f ]]).
Proof.
  use make_z_iso_disp.
  - use (cartesian_factorisation (cleaving_of_types C _ _ (s · f) B)).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (!(id_left _))
             (comp_cat_subst A s ;; ff)%mor_disp).
  - simple refine (_ ,, _ ,, _).
    + use (cartesian_factorisation (cleaving_of_types C _ _ s A)).
      refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (comp_cat_subst B (s · f) ;; inv_mor_disp_from_z_iso ff)%mor_disp).
      abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite z_iso_inv_after_z_iso ;
         rewrite id_left, id_right ;
         apply idpath).
    + abstract
        (use (cartesian_factorisation_unique (cleaving_of_types C _ _ (s · f) B)) ;
         unfold transportb ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite id_left_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite assoc_disp_var ;
         rewrite cartesian_factorisation_commutes ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         unfold comp_cat_subst ;
         rewrite assoc_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite cartesian_factorisation_commutes ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         rewrite assoc_disp_var ;
         rewrite z_iso_disp_after_inv_mor ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite !transport_f_f ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (use (cartesian_factorisation_unique (cleaving_of_types C _ _ s A)) ;
         unfold transportb ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite id_left_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite assoc_disp_var ;
         rewrite (cartesian_factorisation_commutes (cleaving_of_types C Δ Γ s A)) ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         unfold comp_cat_subst ;
         rewrite assoc_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite cartesian_factorisation_commutes ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         rewrite assoc_disp_var ;
         rewrite inv_mor_after_z_iso_disp ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite !transport_f_f ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

(** * 2. Terms in comprehension categories *)
Definition comp_cat_tm
           {C : comp_cat}
           (Γ : C)
           (A : ty Γ)
  : UU
  := ∑ (t : Γ --> Γ & A), t · π A = identity Γ.

Notation "'tm'" := comp_cat_tm : comp_cat.

Definition make_comp_cat_tm
           {C : comp_cat}
           {Γ : C}
           {A : ty Γ}
           (t : Γ --> Γ & A)
           (p : t · π A = identity Γ)
  : tm Γ A
  := t ,, p.

Coercion comp_cat_tm_to_mor
         {C : comp_cat}
         {Γ : C}
         {A : ty Γ}
         (t : tm Γ A)
  : Γ --> Γ & A.
Proof.
  exact (pr1 t).
Defined.

Proposition comp_cat_tm_eq
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            (t : tm Γ A)
  : t · π A = identity Γ.
Proof.
  exact (pr2 t).
Qed.

Proposition eq_comp_cat_tm
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            {t₁ t₂ : tm Γ A}
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

Proposition isaset_comp_cat_tm
            {C : comp_cat}
            (Γ : C)
            (A : ty Γ)
  : isaset (tm Γ A).
Proof.
  use isaset_total2.
  - apply homset_property.
  - intro.
    apply isasetaprop.
    apply homset_property.
Qed.

Definition sub_to_extension
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (s : Δ --> Γ)
           (t : tm Δ (A [[ s ]]))
  : Δ --> Γ & A
  := t · PullbackPr1 (comp_cat_pullback A s).

Proposition sub_to_extension_pr
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (s : Δ --> Γ)
            (t : tm Δ (A [[ s ]]))
  : s = sub_to_extension s t · π A.
Proof.
  unfold sub_to_extension.
  cbn.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply comprehension_functor_mor_comm.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply comp_cat_tm_eq.
  }
  apply id_left.
Qed.

Definition sub_to_extension_tm
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (s : Δ --> Γ & A)
  : tm Δ (A [[ s · π _ ]]).
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
           (t : tm Δ (A [[ s₁ ]]))
  : tm Δ (A [[ s₂ ]]).
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

Definition subst_comp_cat_tm
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (t : tm Γ A)
           (s : Δ --> Γ)
  : tm Δ (A [[ s ]]).
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

Notation "t [[ s ]]tm" := (subst_comp_cat_tm t s) (at level 20).

Proposition subst_comp_cat_tm_pr1
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (t : tm Γ A)
            (s : Δ --> Γ)
  : t [[ s ]]tm · PullbackPr1 (comp_cat_pullback A s) = s · t.
Proof.
  apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A s)).
Qed.

Proposition subst_comp_cat_tm_pr2
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (t : comp_cat_tm Γ A)
            (s : Δ --> Γ)
  : t [[ s ]]tm · π _ = identity _.
Proof.
  apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A s)).
Qed.

(** * 3. Coercion of terms *)
Definition coerce_comp_cat_tm
           {C : comp_cat}
           {Γ : C}
           {A B : ty Γ}
           (f : A <: B)
           (t : tm Γ A)
  : tm Γ B.
Proof.
  use make_comp_cat_tm.
  - exact (t · comp_cat_comp_mor f).
  - abstract
      (rewrite !assoc' ;
       rewrite comp_cat_comp_mor_comm ;
       rewrite comp_cat_tm_eq ;
       apply idpath).
Defined.

Notation "t ↑ f" := (coerce_comp_cat_tm f t) (at level 29, left associativity).

Proposition id_coerce_comp_cat_tm
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            (t : tm Γ A)
  : t ↑ id_disp _ = t.
Proof.
  use eq_comp_cat_tm ; cbn.
  rewrite comp_cat_comp_mor_id.
  apply id_right.
Qed.

Proposition comp_coerce_comp_cat_tm
            {C : comp_cat}
            {Γ : C}
            {A₁ A₂ A₃ : ty Γ}
            (f : A₁ <: A₂)
            (g : A₂ <: A₃)
            (t : tm Γ A₁)
  : t ↑ f ↑ g
    =
    t ↑ (f · g).
Proof.
  use eq_comp_cat_tm ; cbn -[compose].
  rewrite assoc'.
  apply maponpaths.
  refine (!_).
  apply comp_cat_comp_mor_comp.
Qed.

(** * 4. Substitution and coherence *)
Definition id_subst_ty_iso
           {C : comp_cat}
           {Γ : C}
           (A : ty Γ)
  : z_iso (C := fiber_category _ _) A (A [[ identity _ ]]).
Proof.
  exact (nat_z_iso_pointwise_z_iso
           (nat_z_iso_fiber_functor_from_cleaving_identity (cleaving_of_types C) Γ)
           A).
Defined.

Definition id_subst_ty
           {C : comp_cat}
           {Γ : C}
           (A : ty Γ)
  : A <: A [[ identity _ ]]
  := (id_subst_ty_iso A : _ --> _).

Definition id_subst_ty_inv
           {C : comp_cat}
           {Γ : C}
           (A : ty Γ)
  : A [[ identity _ ]] <: A
  := inv_from_z_iso (id_subst_ty_iso A).

Definition comp_subst_ty_iso
           {C : comp_cat}
           {Γ₁ Γ₂ Γ₃ : C}
           (s₁ : Γ₁ --> Γ₂)
           (s₂ : Γ₂ --> Γ₃)
           (A : ty Γ₃)
  : z_iso
      (C := fiber_category _ _)
      (A [[ s₂ ]] [[ s₁ ]])
      (A [[ s₁ · s₂ ]]).
Proof.
  exact (nat_z_iso_pointwise_z_iso
           (fiber_functor_from_cleaving_comp_nat_z_iso (cleaving_of_types C) s₂ s₁)
           A).
Defined.

Definition comp_subst_ty
           {C : comp_cat}
           {Γ₁ Γ₂ Γ₃ : C}
           (s₁ : Γ₁ --> Γ₂)
           (s₂ : Γ₂ --> Γ₃)
           (A : ty Γ₃)
  : A [[ s₂ ]] [[ s₁ ]] <: A [[ s₁ · s₂ ]]
  := (comp_subst_ty_iso s₁ s₂ A : _ --> _).

Definition comp_subst_ty_inv
           {C : comp_cat}
           {Γ₁ Γ₂ Γ₃ : C}
           (s₁ : Γ₁ --> Γ₂)
           (s₂ : Γ₂ --> Γ₃)
           (A : ty Γ₃)
  : A [[ s₁ · s₂ ]] <: A [[ s₂ ]] [[ s₁ ]]
  := inv_from_z_iso (comp_subst_ty_iso s₁ s₂ A).

Definition eq_subst_ty_iso
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           {s₁ s₂ : Γ₁ --> Γ₂}
           (A : ty Γ₂)
           (p : s₁ = s₂)
  : z_iso (C := fiber_category _ _) (A [[ s₁ ]]) (A [[ s₂ ]]).
Proof.
  exact (nat_z_iso_pointwise_z_iso
           (fiber_functor_on_eq_nat_z_iso (cleaving_of_types C) p)
           A).
Defined.

Definition eq_subst_ty
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           {s₁ s₂ : Γ₁ --> Γ₂}
           (A : ty Γ₂)
           (p : s₁ = s₂)
  : A [[ s₁ ]] <: A [[ s₂ ]]
  := (eq_subst_ty_iso A p : _ --> _).

Definition subst_ty_eq_disp_iso
           {C : comp_cat}
           {Γ Δ : C}
           {s s' : Γ --> Δ}
           (A : ty Δ)
           (p : s = s')
  : z_iso_disp
      (identity_z_iso _)
      (A [[ s ]])
      (A [[ s' ]]).
Proof.
  use z_iso_disp_from_z_iso_fiber.
  exact (eq_subst_ty_iso A p).
Defined.

Proposition subst_ty_eq_disp_iso_comm
            {C : comp_cat}
            {Γ Δ : C}
            {s s' : Γ --> Δ}
            (p : s = s')
            (A : ty Δ)
  : (subst_ty_eq_disp_iso A p ;; cleaving_of_types C Δ Γ s' A)%mor_disp
    =
    transportf (λ z, _ -->[ z ] _) (p @ !(id_left _)) (cleaving_of_types C Δ Γ s A).
Proof.
  induction p ; cbn.
  rewrite id_left_disp.
  apply idpath.
Qed.

Proposition subst_ty_eq_disp_iso_inv_comm
            {C : comp_cat}
            {Γ Δ : C}
            {s s' : Γ --> Δ}
            (p : s' = s)
            (A : ty Δ)
  : (inv_mor_disp_from_z_iso (subst_ty_eq_disp_iso A p)
     ;; cleaving_of_types C Δ Γ s' A)%mor_disp
    =
    transportf (λ z, _ -->[ z ] _) (!p @ !(id_left _)) (cleaving_of_types C Δ Γ s A).
Proof.
  induction p ; cbn.
  rewrite id_left_disp.
  apply idpath.
Qed.

Definition eq_subst_ty_inv
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           {s₁ s₂ : Γ₁ --> Γ₂}
           (A : ty Γ₂)
           (p : s₁ = s₂)
  : A [[ s₂ ]] <: A [[ s₁ ]]
  := inv_from_z_iso (eq_subst_ty_iso A p).

Proposition eq_subst_ty_idpath
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            {s : Γ₁ --> Γ₂}
            (A : ty Γ₂)
            (p : s = s)
  : eq_subst_ty A p = identity _.
Proof.
  assert (p = idpath _) as ->.
  {
    apply homset_property.
  }
  cbn.
  apply idpath.
Qed.

Proposition eq_subst_ty_concat
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            {s₁ s₂ s₃ : Γ₁ --> Γ₂}
            (A : ty Γ₂)
            (p : s₁ = s₂)
            (q : s₂ = s₃)
  : eq_subst_ty A p · eq_subst_ty _ q = eq_subst_ty A (p @ q).
Proof.
  induction p, q ; cbn.
  rewrite id_right_disp.
  apply transportfbinv.
Qed.

Proposition eq_subst_ty_eq
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            {s₁ s₂ : Γ₁ --> Γ₂}
            (A : ty Γ₂)
            (p q : s₁ = s₂)
  : eq_subst_ty A p = eq_subst_ty A q.
Proof.
  assert (p = q) as ->.
  {
    apply homset_property.
  }
  apply idpath.
Qed.

Definition coerce_subst_ty
           {C : comp_cat}
           {Γ₁ Γ₂ : C}
           (s : Γ₁ --> Γ₂)
           {A B : ty Γ₂}
           (f : A <: B)
  : A [[ s ]] <: B [[ s ]]
  := #(fiber_functor_from_cleaving _ (cleaving_of_types C) s) f.

Proposition id_coerce_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            (A : ty Γ₂)
  : coerce_subst_ty s (identity (A : fiber_category _ _)) = identity _.
Proof.
  apply (functor_id (fiber_functor_from_cleaving _ (cleaving_of_types C) s)).
Qed.

Proposition comp_coerce_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            {A₁ A₂ A₃ : ty Γ₂}
            (f : A₁ <: A₂)
            (g : A₂ <: A₃)
  : coerce_subst_ty s (f · g)
    =
    coerce_subst_ty s f · coerce_subst_ty s g.
Proof.
  apply (functor_comp (fiber_functor_from_cleaving _ (cleaving_of_types C) s)).
Qed.

Proposition id_right_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            (A : ty Γ₂)
  : coerce_subst_ty s (id_subst_ty A)
    · comp_subst_ty s (identity _) A
    · eq_subst_ty A (id_right _)
    =
    identity _.
Proof.
  exact (!(indexed_cat_lunitor (cleaving_to_indexed_cat _ (cleaving_of_types C)) _ _)).
Qed.

Proposition id_left_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            (A : ty Γ₂)
  : id_subst_ty (A [[ s ]])
    · comp_subst_ty (identity _) s A
    · eq_subst_ty A (id_left _)
    =
    identity _.
Proof.
  exact (!(indexed_cat_runitor (cleaving_to_indexed_cat _ (cleaving_of_types C)) _ _)).
Qed.

Proposition assoc'_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ Γ₄ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (s₃ : Γ₃ --> Γ₄)
            (A : ty Γ₄)
  : comp_subst_ty s₁ s₂ (A [[ s₃ ]])
    · comp_subst_ty (s₁ · s₂) s₃ A
    · eq_subst_ty A (assoc' _ _ _)
    =
    coerce_subst_ty s₁ (comp_subst_ty s₂ s₃ A)
    · comp_subst_ty s₁ (s₂ · s₃) A.
Proof.
  exact (indexed_cat_lassociator (cleaving_to_indexed_cat _ (cleaving_of_types C)) _ _ _ _).
Qed.

Proposition assoc_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ Γ₄ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (s₃ : Γ₃ --> Γ₄)
            (A : ty Γ₄)
  : comp_subst_ty s₁ s₂ (A [[ s₃ ]])
    · comp_subst_ty (s₁ · s₂) s₃ A
    =
    coerce_subst_ty s₁ (comp_subst_ty s₂ s₃ A)
    · comp_subst_ty s₁ (s₂ · s₃) A
    · eq_subst_ty A (assoc _ _ _).
Proof.
  rewrite <- assoc'_subst_ty.
  refine (!(id_right _) @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite eq_subst_ty_concat.
  rewrite eq_subst_ty_idpath.
  apply idpath.
Qed.

Proposition coerce_comp_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ s₂' : Γ₂ --> Γ₃)
            (p : s₂' = s₂)
            (A : ty Γ₃)
  : coerce_subst_ty s₁ (eq_subst_ty _ p) · comp_subst_ty _ s₂ A
    =
    comp_subst_ty _ _ A · eq_subst_ty _ (maponpaths (λ z, _ · z) p).
Proof.
  induction p.
  refine (_ @ id_left _ @ !(id_right _)).
  apply maponpaths_2.
  apply id_coerce_subst_ty.
Qed.

Proposition id_subst_ty_natural
            {C : comp_cat}
            {Γ : C}
            {A B : ty Γ}
            (s : A <: B)
  : id_subst_ty A · coerce_subst_ty _ s
    =
    s · id_subst_ty B.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  cbn.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite id_left_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_subst_ty_natural
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ : C}
            {A B : ty Γ₃}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (f : A <: B)
  : comp_subst_ty s₁ s₂ A
    · coerce_subst_ty _ f
    =
    coerce_subst_ty s₁ (coerce_subst_ty s₂ f)
    · comp_subst_ty s₁ s₂ B.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  cbn.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !assoc_disp_var.
  rewrite !transport_f_f.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite !assoc_disp_var.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition id_sub_comp_cat_tm
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            (t : tm Γ A)
  : t [[ identity _ ]]tm
    =
    t ↑ (id_subst_ty A).
Proof.
  use eq_comp_cat_tm ; cbn.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn.
    rewrite !assoc'.
    rewrite id_left.
    refine (_ @ id_right _).
    apply maponpaths.
    unfold comp_cat_comp_mor.
    etrans.
    {
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite cartesian_factorisation_commutes.
    refine (_ @ comprehension_functor_mor_id _ _).
    unfold comprehension_functor_mor, transportb.
    rewrite disp_functor_transportf, transportf_cod_disp.
    apply idpath.
  - cbn.
    rewrite !assoc'.
    rewrite comp_cat_comp_mor_comm.
    apply comp_cat_tm_eq.
Qed.

Proposition comp_sub_comp_cat_tm
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            {A : ty Γ₃}
            (t : tm Γ₃ A)
  : t [[ s₁ · s₂ ]]tm
    =
    t [[ s₂ ]]tm [[ s₁ ]]tm ↑ (comp_subst_ty s₁ s₂ A).
Proof.
  use eq_comp_cat_tm ; cbn.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A _))).
  - cbn.
    unfold comp_cat_comp_mor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite cartesian_factorisation_commutes.
    unfold comprehension_functor_mor, transportb.
    rewrite disp_functor_transportf, transportf_cod_disp.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (PullbackArrow_PullbackPr1 (comp_cat_pullback (A [[s₂]]) s₁)).
    }
    rewrite !assoc'.
    apply maponpaths.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A s₂)).
  - cbn.
    rewrite !assoc'.
    rewrite comp_cat_comp_mor_comm.
    apply (PullbackArrow_PullbackPr2 (comp_cat_pullback (A [[s₂]]) s₁)).
Qed.

Proposition subst_coerce_comp_cat_tm
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            {A₁ A₂ : ty Γ₂}
            (s : Γ₁ --> Γ₂)
            (f : A₁ <: A₂)
            (t : comp_cat_tm Γ₂ A₁)
  : (t ↑ f) [[ s ]]tm
    =
    t [[ s ]]tm ↑ coerce_subst_ty s f.
Proof.
  use eq_comp_cat_tm.
  cbn -[coerce_subst_ty].
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A₂ s))).
  - unfold comp_cat_comp_mor.
    cbn -[coerce_subst_ty].
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A₁ s)).
  - rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_comp_mor_comm.
    }
    apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A₁ s)).
Qed.

(** * 5. Variable rule *)
Definition comp_cat_tm_var
           {C : comp_cat}
           (Γ : C)
           (A : ty Γ)
  : tm (Γ & A) (A [[ π _ ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback _ _)).
    + apply identity.
    + apply identity.
    + abstract
        (rewrite !id_left ;
         apply idpath).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
Defined.

Definition subst_comp_cat_tm_var_coerce
           {C : comp_cat}
           {Γ Δ : C}
           {A : ty Γ}
           (s : Δ --> Γ)
           (t : tm Δ (A [[ s ]]))
  : A [[s]] <: (A [[ π A ]]) [[ sub_to_extension s t ]].
Proof.
  refine (eq_subst_ty _ _ · comp_subst_ty_inv _ _ _).
  apply sub_to_extension_pr.
Defined.

Lemma cleaving_of_types_eq
      {C : comp_cat}
      {Γ Δ : C}
      {s s' : Δ --> Γ}
      (p : s = s')
      (A : ty Γ)
  : (pr1 (idtoiso
            (C := fiber_category _ _)
            (maponpaths (λ z, pr1 (cleaving_of_types _ _ _ z _)) p))
    ;; cleaving_of_types C Γ Δ s' A
    =
    transportf
      (λ z, _ -->[ z ] _)
      (p @ !(id_left _))
      (cleaving_of_types C Γ Δ s A))%mor_disp.
Proof.
  induction p ; cbn.
  rewrite id_left_disp.
  apply idpath.
Qed.

Proposition subst_comp_cat_tm_var
            {C : comp_cat}
            {Γ Δ : C}
            {A : ty Γ}
            (s : Δ --> Γ)
            (t : tm Δ (A [[ s ]]))
  : comp_cat_tm_var Γ A [[ sub_to_extension s t ]]tm
    =
    t ↑ subst_comp_cat_tm_var_coerce s t.
Proof.
  use eq_comp_cat_tm.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn -[eq_subst_ty comp_subst_ty compose].
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback A (π A)))).
    + cbn -[eq_subst_ty comp_subst_ty compose].
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A (π A))).
      }
      rewrite id_right.
      unfold sub_to_extension.
      apply maponpaths.
      cbn -[eq_subst_ty comp_subst_ty compose].
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      {
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      {
        apply maponpaths.
        rewrite assoc_disp.
        apply maponpaths.
        cbn.
        unfold fiber_functor_from_cleaving_comp_inv.
        rewrite !mor_disp_transportf_postwhisker.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          rewrite assoc_disp_var.
          rewrite cartesian_factorisation_commutes.
          apply idpath.
        }
        rewrite mor_disp_transportf_postwhisker.
        apply maponpaths.
        rewrite assoc_disp_var.
        apply maponpaths.
        rewrite cartesian_factorisation_commutes.
        rewrite mor_disp_transportf_prewhisker.
        apply idpath.
      }
      unfold transportb.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        apply cleaving_of_types_eq.
      }
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    + cbn -[eq_subst_ty comp_subst_ty compose].
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply comprehension_functor_mor_comm.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply comp_cat_comp_mor_comm.
      }
      rewrite !assoc.
      rewrite comp_cat_tm_eq.
      rewrite id_left.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A (π A))).
      }
      apply id_right.
  - cbn -[eq_subst_ty comp_subst_ty compose].
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_comp_mor_comm.
    }
    apply comp_cat_tm_eq.
Qed.

(** * 6. Notations and accessors for functors of comprehension categories *)
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

Definition comp_cat_functor_empty_context_z_iso
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
  : z_iso (F []) []
  := _ ,, comp_cat_functor_empty_context_is_z_iso F.

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

Definition comp_cat_functor_subst_ty
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ Δ : C₁}
           (s : Γ --> Δ)
           (A : ty Δ)
  : z_iso_disp
      (identity_z_iso _)
      (comp_cat_type_functor F _ (A [[ s ]]))
      ((comp_cat_type_functor F _ A) [[ #F s ]]).
Proof.
  apply (cartesian_disp_functor_disp_z_iso
           (cartesian_comp_cat_type_functor F)).
Defined.

Definition comp_cat_functor_subst_ty_z_iso
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ Δ : C₁}
           (s : Γ --> Δ)
           (A : ty Δ)
  : z_iso
      (C := fiber_category _ _)
      (comp_cat_type_functor F _ (A [[ s ]]))
      ((comp_cat_type_functor F _ A) [[ #F s ]]).
Proof.
  use z_iso_fiber_from_z_iso_disp.
  exact (comp_cat_functor_subst_ty F s A).
Defined.

Definition comp_cat_functor_subst_ty_coe
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ Δ : C₁}
           (s : Γ --> Δ)
           (A : ty Δ)
  : comp_cat_type_functor F _ (A [[ s ]]) <: (comp_cat_type_functor F _ A) [[ #F s ]]
  := (comp_cat_functor_subst_ty_z_iso F s A : _ --> _).

Definition comp_cat_functor_subst_ty_inv_coe
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ Δ : C₁}
           (s : Γ --> Δ)
           (A : ty Δ)
  : (comp_cat_type_functor F _ A) [[ #F s ]] <: comp_cat_type_functor F _ (A [[ s ]])
  := inv_from_z_iso (comp_cat_functor_subst_ty_z_iso F s A).

Definition comp_cat_functor_tm
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ : C₁}
           {A : ty Γ}
           (t : tm Γ A)
  : tm (F Γ) (comp_cat_type_functor F _ A).
Proof.
  use make_comp_cat_tm.
  - exact (#F t · comprehension_nat_trans_mor (comp_cat_functor_comprehension F) A).
  - abstract
      (rewrite assoc' ;
       refine (maponpaths (λ z, _ · z) (comprehension_nat_trans_mor_comm _ _ _) @ _) ;
       rewrite <- functor_comp ;
       rewrite <- functor_id ;
       apply maponpaths ;
       apply comp_cat_tm_eq).
Defined.

Proposition id_comp_cat_functor_tm
            {C : comp_cat}
            {Γ : C}
            {A : ty Γ}
            (t : tm Γ A)
  : comp_cat_functor_tm (identity C) t = t.
Proof.
  use eq_comp_cat_tm ; cbn.
  apply id_right.
Qed.

Definition comp_comp_cat_functor_tm
           {C₁ C₂ C₃ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           (G : comp_cat_functor C₂ C₃)
           {Γ : C₁}
           {A : ty Γ}
           (t : tm Γ A)
  : comp_cat_functor_tm (F · G) t
    =
    comp_cat_functor_tm G (comp_cat_functor_tm F t).
Proof.
  use eq_comp_cat_tm ; cbn.
  rewrite !assoc.
  rewrite functor_comp.
  apply idpath.
Qed.

Definition comp_cat_functor_coerce
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ : C₁}
           {A B : ty Γ}
           (s : A <: B)
  : comp_cat_type_functor F Γ A <: comp_cat_type_functor F Γ B
  := #(fiber_functor (comp_cat_type_functor F) Γ) s.

Proposition comp_cat_functor_coerce_on_id
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_functor_coerce F (identity (C := fiber_category _ _) A) = identity _.
Proof.
  apply (functor_id (fiber_functor (comp_cat_type_functor F) Γ)).
Qed.

Proposition comp_cat_functor_coerce_on_comp
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ : C₁}
            {A₁ A₂ A₃ : ty Γ}
            (s₁ : A₁ <: A₂)
            (s₂ : A₂ <: A₃)
  : comp_cat_functor_coerce F (s₁ · s₂)
    =
    comp_cat_functor_coerce F s₁ · comp_cat_functor_coerce F s₂.
Proof.
  apply (functor_comp (fiber_functor (comp_cat_type_functor F) Γ)).
Qed.

Proposition comp_cat_functor_coerce_tm
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ : C₁}
            {A B : ty Γ}
            (s : A <: B)
            (t : tm Γ A)
  : comp_cat_functor_tm F (t ↑ s)
    =
    comp_cat_functor_tm F t ↑ comp_cat_functor_coerce F s.
Proof.
  use eq_comp_cat_tm ; cbn.
  rewrite functor_comp.
  rewrite !assoc'.
  apply maponpaths.
  unfold comp_cat_comp_mor.
  rewrite comprehension_functor_mor_transportf.
  apply comprehension_nat_trans_comm.
Qed.

Proposition comp_cat_functor_subst_tm
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ Δ : C₁}
            {A : ty Δ}
            (s : Γ --> Δ)
            (t : tm Δ A)
  : comp_cat_functor_tm F (t [[ s ]]tm) ↑ (comp_cat_functor_subst_ty_coe F s A)
    =
    comp_cat_functor_tm F t [[ #F s ]]tm.
Proof.
  use eq_comp_cat_tm.
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn ; unfold comp_cat_comp_mor.
    etrans.
    {
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      {
        do 3 apply maponpaths.
        apply cartesian_factorisation_commutes.
      }
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply comprehension_nat_trans_comm.
      }
      rewrite !assoc.
      rewrite <- functor_comp.
      apply maponpaths_2.
      apply maponpaths.
      apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A s)).
    }
    rewrite functor_comp.
    rewrite assoc'.
    apply idpath.
  - cbn ; unfold comp_cat_comp_mor.
    etrans.
    {
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply comprehension_functor_mor_comm.
      }
      rewrite id_right.
      etrans.
      {
        apply maponpaths.
        apply comprehension_nat_trans_mor_comm.
      }
      rewrite <- functor_comp.
      apply maponpaths.
      apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A s)).
    }
    apply functor_id.
Qed.

Proposition comp_cat_functor_subst_tm_alt
            {C₁ C₂ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            {Γ Δ : C₁}
            {A : ty Δ}
            (s : Γ --> Δ)
            (t : tm Δ A)
  : comp_cat_functor_tm F (t [[ s ]]tm)
    =
    comp_cat_functor_tm F t [[ #F s ]]tm ↑ (comp_cat_functor_subst_ty_inv_coe F s A).
Proof.
  rewrite <- comp_cat_functor_subst_tm.
  rewrite comp_coerce_comp_cat_tm.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply z_iso_inv_after_z_iso.
  }
  apply id_coerce_comp_cat_tm.
Qed.

Proposition id_comp_cat_functor_coerce
            {C : comp_cat}
            {Γ : C}
            {A B : ty Γ}
            (s : A <: B)
  : comp_cat_functor_coerce (identity C) s = s.
Proof.
  apply idpath.
Qed.

Proposition id_comp_cat_functor_subst_ty_coe
            {C : comp_cat}
            {Γ Δ : C}
            (s : Γ --> Δ)
            (A : ty Δ)
  : comp_cat_functor_subst_ty_coe (identity C) s A = identity _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  cbn ; unfold fiber_functor_natural_inv ; cbn.
  rewrite cartesian_factorisation_commutes.
  rewrite id_left_disp.
  unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_comp_cat_functor_coerce
            {C₁ C₂ C₃ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            (G : comp_cat_functor C₂ C₃)
            {Γ : C₁}
            {A B : ty Γ}
            (s : A <: B)
  : comp_cat_functor_coerce (F · G) s
    =
    comp_cat_functor_coerce G (comp_cat_functor_coerce F s).
Proof.
  cbn.
  rewrite disp_functor_transportf.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_comp_cat_functor_subst_ty_coe
            {C₁ C₂ C₃ : comp_cat}
            (F : comp_cat_functor C₁ C₂)
            (G : comp_cat_functor C₂ C₃)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (A : ty Δ)
  : comp_cat_functor_subst_ty_coe (F · G) s A
    =
    comp_cat_functor_coerce G (comp_cat_functor_subst_ty_coe F s A)
    · comp_cat_functor_subst_ty_coe G (#F s) (comp_cat_type_functor F Δ A).
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)) ; cbn.
  unfold fiber_functor_natural_inv.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite <- disp_functor_comp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite disp_functor_transportf.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition comp_cat_functor_subst_ty_natural
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           {Γ Δ : C₁}
           (s : Γ --> Δ)
           {A B : ty Δ}
           (f : A <: B)
  : comp_cat_functor_coerce F (coerce_subst_ty s f)
    · comp_cat_functor_subst_ty_coe F s B
    =
    comp_cat_functor_subst_ty_coe F s A
    · coerce_subst_ty (#F s) (comp_cat_functor_coerce F f).
Proof.
  cbn.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !assoc_disp_var.
  rewrite !transport_f_f.
  unfold fiber_functor_natural_inv.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite <- !disp_functor_comp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite disp_functor_transportf.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

(** * 7. Notations and accessors for natural transformations of comprehension categories *)
Proposition comp_cat_nat_trans_subst_path
            {C₁ C₂ : comp_cat}
            {F G : comp_cat_functor C₁ C₂}
            (τ : comp_cat_nat_trans F G)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
  : identity (F Γ) · # F s · τ Δ = τ Γ · identity (G Γ) · # G s.
Proof.
  rewrite id_left, id_right.
  exact (nat_trans_ax τ _ _ s).
Qed.

Proposition comp_cat_nat_trans_subst
            {C₁ C₂ : comp_cat}
            {F G : comp_cat_functor C₁ C₂}
            (τ : comp_cat_nat_trans F G)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (A : ty Δ)
  : (comp_cat_type_nat_trans τ Γ (A [[ s ]])
     ;; comp_cat_functor_subst_ty_coe G s A
     ;; comp_cat_subst _ _)%mor_disp
    =
    transportf
      (λ z, _ -->[ z ] _)
      (comp_cat_nat_trans_subst_path τ s)
      (comp_cat_functor_subst_ty_coe F s A
       ;; comp_cat_subst _ _
       ;; comp_cat_type_nat_trans τ Δ A)%mor_disp.
Proof.
  cbn.
  unfold fiber_functor_natural_inv.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite assoc_disp_var.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply (disp_nat_trans_ax_var (comp_cat_type_nat_trans τ) (cleaving_of_types _ _ _ _ _)).
  }
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_nat_trans_subst_alt
            {C₁ C₂ : comp_cat}
            {F G : comp_cat_functor C₁ C₂}
            (τ : comp_cat_nat_trans F G)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (A : ty Δ)
  : (comp_cat_functor_subst_ty_coe F s A
     ;; comp_cat_subst _ _
     ;; comp_cat_type_nat_trans τ Δ A)%mor_disp
    =
    transportf
      (λ z, _ -->[ z ] _)
      (!(comp_cat_nat_trans_subst_path τ s))
      (comp_cat_type_nat_trans τ Γ (A [[ s ]])
       ;; comp_cat_functor_subst_ty_coe G s A
       ;; comp_cat_subst _ _)%mor_disp.
Proof.
  rewrite comp_cat_nat_trans_subst.
  rewrite transport_f_f.
  refine (!_).
  apply transportf_set.
  apply homset_property.
Qed.

Definition comp_cat_type_fib_nat_trans
           {C₁ C₂ : comp_cat}
           {F G : comp_cat_functor C₁ C₂}
           (τ : comp_cat_nat_trans F G)
           {Γ : C₁}
           (A : ty Γ)
  : comp_cat_type_functor F Γ A <: comp_cat_type_functor G Γ A [[ τ Γ ]].
Proof.
  use (cartesian_factorisation (cleaving_of_types _ _ _ _ _)).
  exact (transportf
           (λ z, _ -->[ z ] _)
           (!(id_left _))
           (comp_cat_type_nat_trans τ Γ A)).
Defined.

Proposition comp_cat_type_fib_nat_trans_coerce
            {C₁ C₂ : comp_cat}
            {F G : comp_cat_functor C₁ C₂}
            (τ : comp_cat_nat_trans F G)
            {Γ : C₁}
            {A B : ty Γ}
            (s : A <: B)
  : comp_cat_type_fib_nat_trans τ A
    · coerce_subst_ty (τ Γ) (comp_cat_functor_coerce G s)
    =
    comp_cat_functor_coerce F s
    · comp_cat_type_fib_nat_trans τ B.
Proof.
  cbn.
  rewrite mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !assoc_disp_var.
  rewrite !transport_f_f.
  unfold comp_cat_type_fib_nat_trans.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply (disp_nat_trans_ax_var (comp_cat_type_nat_trans τ)).
  }
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition comp_cat_nat_trans_tm
           {C₁ C₂ : comp_cat}
           {F G : comp_cat_functor C₁ C₂}
           (τ : comp_cat_nat_trans F G)
           {Γ : C₁}
           {A : ty Γ}
           (t : tm Γ A)
  : comp_cat_functor_tm F t ↑ comp_cat_type_fib_nat_trans τ A
    =
    comp_cat_functor_tm G t [[τ Γ ]]tm.
Proof.
  use eq_comp_cat_tm ; cbn.
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn.
    rewrite !assoc.
    rewrite <- (nat_trans_ax τ _ _ t).
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite comprehension_functor_mor_transportf.
    exact (comp_cat_nat_trans_comprehension τ A).
  - cbn.
    rewrite !assoc'.
    rewrite comp_cat_comp_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply comprehension_nat_trans_mor_comm.
    }
    rewrite <- functor_comp.
    rewrite <- functor_id.
    apply maponpaths.
    apply comp_cat_tm_eq.
Qed.
