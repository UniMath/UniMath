(*************************************************************************************

 Accessors for full DFL comprehension categories

 In this file, we define numerous useful accessors for full DFL comprehension categories.
 First, we show that terms and displayed morphisms from the identity are equivalent.
 Here, we use that the comprehension category is full (so, the comprehension functor is
 fully faithful) and we use that the unit type is strong (extending with the unit type
 gives an isomorphic context).

 For democracy and sigma types, we only give basic accessors. However, we define more
 interesting operations for equalizer types. More specifically, we construct some kind
 of identity type: whenever we have two terms, then we can form their identity type. Here
 we use that terms correspond to displayed morphisms, and that we have fiberwise
 equalizers. Since we are using equalizers, some diagram involving the projections will
 commute ([dfl_ext_identity_eq]). We also give an introduction rule for terms of this
 identity type ([dfl_ext_identity_type_tm]), and we look at stability under substitution
 ([dfl_ext_identity_sub_tm]). Finally, we show that every term of the identity type is
 equal ([dfl_eq_subst_equalizer_tm]). It is good to note that here we consistently use
 equality of morphisms. For that reason, this constructed identity type is extensional.

 Contents
 1. Terms and displayed morphisms
 2. Operations on democracy
 3. Operations on extensional identity types
 4. Operations on sigma types

 *************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FullyFaithfulDispFunctor.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

Section DFLCompCat.
  Context {C : dfl_full_comp_cat}.

  (** * 1. Terms and displayed morphisms *)
  Section TmAndMor.
    Context {Γ : C}
            {A : ty Γ}.

    Definition dfl_full_comp_cat_mor_to_tm
               (f : dfl_full_comp_cat_unit Γ -->[ identity _ ] A)
      : comp_cat_tm Γ A.
    Proof.
      use make_comp_cat_tm.
      - exact (inv_from_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)
               · comprehension_functor_mor (comp_cat_comprehension C) f).
      - abstract
          (rewrite !assoc' ;
           refine (maponpaths
                     (λ z, _ · z)
                     (comprehension_functor_mor_comm (comp_cat_comprehension C) f)
                   @ _) ;
           rewrite id_right ;
           apply z_iso_after_z_iso_inv).
    Defined.

    Definition dfl_full_comp_cat_tm_to_mor
               (t : comp_cat_tm Γ A)
      : dfl_full_comp_cat_unit Γ -->[ identity _ ] A.
    Proof.
      use (disp_functor_ff_inv
             _
             (full_comp_cat_comprehension_fully_faithful C) _).
      simple refine (_ ,, _).
      - exact (π _ · t).
      - abstract
          (cbn ;
           rewrite id_right ;
           rewrite !assoc' ;
           refine (maponpaths
                     (λ z, _ · z)
                     (comp_cat_tm_eq t)
                   @ _) ;
           apply id_right).
    Defined.

    Proposition dfl_full_comp_cat_mor_to_tm_to_mor
                (f : dfl_full_comp_cat_unit Γ -->[ id₁ Γ] A)
      : dfl_full_comp_cat_tm_to_mor (dfl_full_comp_cat_mor_to_tm f) = f.
    Proof.
      refine (_ @ homotinvweqweq
                    (disp_functor_ff_weq
                       _
                       (full_comp_cat_comprehension_fully_faithful C)
                       _ _ _)
                    _).
      unfold dfl_full_comp_cat_tm_to_mor.
      apply maponpaths.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (z_iso_inv_after_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)).
      }
      apply id_left.
    Qed.

    Proposition dfl_full_comp_cat_tm_to_mor_to_tm
                (t : comp_cat_tm Γ A)
      : dfl_full_comp_cat_mor_to_tm (dfl_full_comp_cat_tm_to_mor t) = t.
    Proof.
      use eq_comp_cat_tm ; cbn.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (FF_disp_functor_ff_inv
                    (full_comp_cat_comprehension_fully_faithful C)
                    _)).
      }
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_after_z_iso_inv.
      }
      apply id_left.
    Qed.
  End TmAndMor.

  Definition dfl_full_comp_cat_tm_weq_mor
             {Γ : C}
             (A : ty Γ)
    : dfl_full_comp_cat_unit Γ -->[ identity _ ] A
      ≃
      comp_cat_tm Γ A.
  Proof.
    use weq_iso.
    - exact dfl_full_comp_cat_mor_to_tm.
    - exact dfl_full_comp_cat_tm_to_mor.
    - exact dfl_full_comp_cat_mor_to_tm_to_mor.
    - exact dfl_full_comp_cat_tm_to_mor_to_tm.
  Defined.

  (** * 2. Operations on democracy *)
  Definition dfl_con_to_ty
             (Γ : C)
    : ty ([] : C)
    := is_democratic_ty (is_democratic_dfl_full_comp_cat C) Γ.

  Definition dfl_con_to_z_iso
             (Γ : C)
    : z_iso Γ ([] & dfl_con_to_ty Γ)
    := is_democratic_iso (is_democratic_dfl_full_comp_cat C) Γ.

  Definition dfl_sub_to_mor
             {Γ Δ : C}
             (s : Γ --> Δ)
    : dfl_con_to_ty Γ -->[ identity _ ] dfl_con_to_ty Δ.
  Proof.
    use (disp_functor_ff_inv
           _
           (full_comp_cat_comprehension_fully_faithful C) _).
    simple refine (_ ,, _).
    - exact (inv_from_z_iso (dfl_con_to_z_iso Γ) · s · dfl_con_to_z_iso Δ).
    - abstract
        (apply TerminalArrowEq).
  Defined.

  (** * 3. Operations on extensional identity types *)
  Definition dfl_ext_identity
             {Γ : C}
             {A : ty Γ}
             (t₁ t₂ : comp_cat_tm Γ A)
    : Equalizer
        (C := fiber_category (disp_cat_of_types C) Γ)
        (dfl_full_comp_cat_tm_to_mor t₁)
        (dfl_full_comp_cat_tm_to_mor t₂)
    := pr1 (fiberwise_equalizers_dfl_full_comp_cat C) Γ _ _ _ _.

  Definition dfl_ext_identity_type
             {Γ : C}
             {A : ty Γ}
             (t₁ t₂ : comp_cat_tm Γ A)
    : ty Γ
    := EqualizerObject (dfl_ext_identity t₁ t₂).

  Proposition dfl_ext_identity_eq
              {Γ : C}
              {A : ty Γ}
              (t₁ t₂ : comp_cat_tm Γ A)
    : π (dfl_ext_identity_type t₁ t₂) · t₁
      =
      π (dfl_ext_identity_type t₁ t₂) · t₂.
  Proof.
    refine (_ @ maponpaths comp_cat_comp_mor (EqualizerEqAr (dfl_ext_identity t₁ t₂)) @ _).
    - cbn.
      unfold comp_cat_comp_mor.
      rewrite comprehension_functor_mor_transportf.
      rewrite comprehension_functor_mor_comp.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (FF_disp_functor_ff_inv
                    (full_comp_cat_comprehension_fully_faithful C)
                    _)).
      }
      cbn.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        exact (comprehension_functor_mor_comm (comp_cat_comprehension C) _).

      }
      apply id_right.
    - cbn.
      unfold comp_cat_comp_mor.
      rewrite comprehension_functor_mor_transportf.
      rewrite comprehension_functor_mor_comp.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (FF_disp_functor_ff_inv
                    (full_comp_cat_comprehension_fully_faithful C)
                    _)).
      }
      cbn.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        exact (comprehension_functor_mor_comm (comp_cat_comprehension C) _).

      }
      apply id_right.
  Qed.

  Definition dfl_ext_identity_type_tm
             {Γ : C}
             {A : ty Γ}
             (t₁ t₂ : comp_cat_tm Γ A)
             (p : π (dfl_full_comp_cat_unit Γ) · t₁
                  =
                  π (dfl_full_comp_cat_unit Γ) · t₂)
    : comp_cat_tm Γ (dfl_ext_identity_type t₁ t₂).
  Proof.
    use dfl_full_comp_cat_mor_to_tm.
    use (EqualizerIn (dfl_ext_identity t₁ t₂)).
    - apply TerminalArrow.
    - use (invmaponpathsweq (dfl_full_comp_cat_tm_weq_mor _)).
      use eq_comp_cat_tm.
      cbn.
      apply maponpaths.
      rewrite !comprehension_functor_mor_transportf.
      rewrite !comprehension_functor_mor_comp.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (FF_disp_functor_ff_inv
                    (full_comp_cat_comprehension_fully_faithful C)
                    _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (FF_disp_functor_ff_inv
                    (full_comp_cat_comprehension_fully_faithful C)
                    _)).
      }
      refine (!_).
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply comprehension_functor_mor_comm.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comprehension_functor_mor_comm.
      }
      refine (!_).
      rewrite !id_right.
      exact p.
  Qed.

  Definition dfl_ext_identity_sub_mor_mor
             {Γ Δ : C}
             (s : Δ --> Γ)
             {A : ty Γ}
             (t₁ t₂ : comp_cat_tm Γ A)
    : (disp_cat_of_types C)[{Δ}]
        ⟦ dfl_ext_identity_type (sub_comp_cat_tm t₁ s) (sub_comp_cat_tm t₂ s)
        , fiber_functor_from_cleaving
            (disp_cat_of_types C)
            (cleaving_of_types C)
            s
            (dfl_full_comp_cat_unit Γ)
        ⟧.
  Proof.
    refine (EqualizerArrow
              (dfl_ext_identity (sub_comp_cat_tm t₁ s) (sub_comp_cat_tm t₂ s))
            · _).
    use (TerminalArrow
           (preserves_terminal_to_terminal
              _
              (pr2 (fiberwise_terminal_dfl_full_comp_cat C) _ _ s)
              _)).
  Defined.

  Proposition dfl_ext_identity_sub_mor_eq
              {Γ Δ : C}
              (s : Δ --> Γ)
              {A : ty Γ}
              (t₁ t₂ : comp_cat_tm Γ A)
    : dfl_ext_identity_sub_mor_mor s t₁ t₂
      · # (fiber_functor_from_cleaving
             (disp_cat_of_types C)
             (cleaving_of_types C)
             s)
          (dfl_full_comp_cat_tm_to_mor t₁)
      =
      dfl_ext_identity_sub_mor_mor s t₁ t₂
      · # (fiber_functor_from_cleaving
             (disp_cat_of_types C)
             (cleaving_of_types C)
             s)
          (dfl_full_comp_cat_tm_to_mor t₂).
  Proof.
    unfold dfl_ext_identity_sub_mor_mor.
    rewrite !assoc'.
    pose (EqualizerEqAr
            (dfl_ext_identity
               (sub_comp_cat_tm t₁ s)
               (sub_comp_cat_tm t₂ s)))
      as p.
    refine (_ @ p @ _) ; apply maponpaths ; clear p.
    - use (invmaponpathsweq (dfl_full_comp_cat_tm_weq_mor _)).
      refine (_ @ !(homotweqinvweq (dfl_full_comp_cat_tm_weq_mor _) _)).
      use eq_comp_cat_tm.
      cbn.
      rewrite comprehension_functor_mor_transportf.
      rewrite comprehension_functor_mor_comp.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (cartesian_to_pullback _ _))).
      + rewrite !assoc'.
        rewrite comprehension_functor_mor_factorisation_pr1.
        rewrite comprehension_functor_mor_transportf.
        rewrite comprehension_functor_mor_comp.
        rewrite PullbackArrow_PullbackPr1.
        etrans.
        {
          do 3 apply maponpaths.
          exact (maponpaths
                   pr1
                   (FF_disp_functor_ff_inv
                      (full_comp_cat_comprehension_fully_faithful C)
                      _)).
        }
        cbn.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite comprehension_functor_mor_comm.
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite comprehension_functor_mor_comm.
        rewrite id_right.
        apply z_iso_after_z_iso_inv.
      + rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply comprehension_functor_mor_factorisation_pr2.
        }
        rewrite id_right.
        rewrite comprehension_functor_mor_comm.
        rewrite id_right.
        rewrite PullbackArrow_PullbackPr2.
        apply z_iso_after_z_iso_inv.
    - use (invmaponpathsweq (dfl_full_comp_cat_tm_weq_mor _)).
      refine (homotweqinvweq (dfl_full_comp_cat_tm_weq_mor _) _ @ _).
      use eq_comp_cat_tm.
      cbn.
      rewrite comprehension_functor_mor_transportf.
      rewrite comprehension_functor_mor_comp.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (cartesian_to_pullback _ _))).
      + rewrite !assoc'.
        rewrite comprehension_functor_mor_factorisation_pr1.
        rewrite comprehension_functor_mor_transportf.
        rewrite comprehension_functor_mor_comp.
        rewrite PullbackArrow_PullbackPr1.
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          exact (maponpaths
                   pr1
                   (FF_disp_functor_ff_inv
                      (full_comp_cat_comprehension_fully_faithful C)
                      _)).
        }
        cbn.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite comprehension_functor_mor_comm.
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite comprehension_functor_mor_comm.
        rewrite id_right.
        apply z_iso_after_z_iso_inv.
      + rewrite !assoc'.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          apply comprehension_functor_mor_factorisation_pr2.
        }
        rewrite id_right.
        rewrite comprehension_functor_mor_comm.
        rewrite id_right.
        rewrite PullbackArrow_PullbackPr2.
        apply z_iso_after_z_iso_inv.
  Qed.

  Definition dfl_ext_identity_sub_mor
             {Γ Δ : C}
             (s : Δ --> Γ)
             {A : ty Γ}
             (t₁ t₂ : comp_cat_tm Γ A)
    : dfl_ext_identity_type (sub_comp_cat_tm t₁ s) (sub_comp_cat_tm t₂ s)
      -->[ identity _ ]
      dfl_ext_identity_type t₁ t₂ [[s]].
  Proof.
    use (EqualizerIn
           (preserves_equalizer_equalizer
              (pr2 (fiberwise_equalizers_dfl_full_comp_cat C) _ _ s)
              (dfl_ext_identity t₁ t₂))).
    - exact (dfl_ext_identity_sub_mor_mor s t₁ t₂).
    - exact (dfl_ext_identity_sub_mor_eq s t₁ t₂).
  Defined.

  Definition dfl_ext_identity_sub_tm
             {Γ Δ : C}
             (s : Δ --> Γ)
             {A : ty Γ}
             {t₁ t₂ : comp_cat_tm Γ A}
             (p : comp_cat_tm
                    Δ
                    (dfl_ext_identity_type
                       (sub_comp_cat_tm t₁ s)
                       (sub_comp_cat_tm t₂ s)))
    : comp_cat_tm Δ ((dfl_ext_identity_type t₁ t₂) [[ s ]]).
  Proof.
    use make_comp_cat_tm.
    - exact (p · comp_cat_comp_mor (dfl_ext_identity_sub_mor s t₁ t₂)).
    - abstract
        (rewrite !assoc' ;
         unfold comp_cat_comp_mor ;
         refine (maponpaths (λ z, _ · z) (comprehension_functor_mor_comm _ _) @ _) ;
         rewrite id_right ;
         apply comp_cat_tm_eq).
  Defined.

  Proposition dfl_eq_subst_equalizer_tm
              {Γ Δ : C}
              (s : Δ --> Γ)
              {A : ty Γ}
              (t₁ t₂ : comp_cat_tm Γ A)
              (p₁ p₂ : comp_cat_tm Δ (dfl_ext_identity_type t₁ t₂ [[ s ]]))
    : p₁ = p₂.
  Proof.
    use (invmaponpathsweq (invweq (dfl_full_comp_cat_tm_weq_mor _))) ; cbn.
    use (EqualizerArrowisMonic
           (preserves_equalizer_equalizer
              (pr2 (fiberwise_equalizers_dfl_full_comp_cat C) _ _ s)
              (dfl_ext_identity t₁ t₂))).
    apply (TerminalArrowEq
             (T := preserves_terminal_to_terminal
                     _
                     (pr2 (fiberwise_terminal_dfl_full_comp_cat C) _ _ s)
                     (dfl_full_comp_cat_terminal _))).
  Qed.

  (** * 4. Operations on sigma types *)
  Definition dfl_sigma_type
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : ty Γ
    := dep_sum (strong_dependent_sum_dfl_full_comp_cat C) (π A) B.

  Definition dfl_sigma_type_strong
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : z_iso (Γ & A & B) (Γ & dfl_sigma_type A B)
    := _ ,, strong_dependent_sums_iso (strong_dependent_sum_dfl_full_comp_cat C) A B.
End DFLCompCat.
