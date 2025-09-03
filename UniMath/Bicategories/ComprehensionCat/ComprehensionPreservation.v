(**

 Preservation by the comprehension functor

 If `C` is a DFL full comprehension category, then it comprehension functor `χ` is an
 adjoint equivalence. This allows us to deduce that it preserves structure and properties
 of the fiber categories, for instance, initial objects and subobject classifiers.

 For the propositional truncation, we take a slight detour. The comprehension functor
 preserves regular epimorphisms, which means that regular epimorphisms between types are
 mapped to regular epimorphisms in the slice category. However, we want to have an
 isomorphism between `Γ & regular_local_property_trunc HC A` and the image of `π A` in `C`.
 To obtain this isomorphism, we must do some extra work.

 We also meet a similar problem for extensional identity types. While we can directly show
 that the comprehension functor preserves equalizers, there is a technical difficulty. More
 specifically, if we write `t₁ =_ext t₂` for the extensional identity type, we want to
 construct an isomorphism between `Γ & t₁ =_ext t₂` and the equalizer of `t₁` and `t₂`.
 However, preservation only gives us that `Γ & t₁ =_ext t₂` is an equalizer of two morphisms
 that are slightly different from `t₁` and `t₂`. In fact, the domain of those morphisms is
 only isomorphism to the domains of `t₁` and `t₂` and not definitionally equal. As a result,
 we are required to connect those two equalizers.

 Contents
 1. Preliminary notions
 2. Preservation of initial objects
 3. Preservation of subobject classifiers
 4. Preservation of parameterized natural number objects
 5. Preservation of binary coproducts
 6. Preservation of truncations
 7. Preservation of extensional identity types

                                                                                          *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRegular.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Preliminary notions *)
Definition dfl_full_comp_cat_adjequiv_base_functor
           (C : dfl_full_comp_cat)
  : dfl_full_comp_cat_fiber ([] : C) ⟶ dfl_full_comp_cat_to_finlim C
  := fiber_functor (comp_cat_comprehension C) []
     ∙ cod_fib_terminal_to_base _.

Definition dfl_full_comp_cat_adjequiv_base_functor_finlim
           (C : dfl_full_comp_cat)
  : functor_finlim (dfl_full_comp_cat_fiber []) (dfl_full_comp_cat_to_finlim C)
  := make_functor_finlim_adjequiv
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base C).

Definition dfl_full_comp_cat_to_cod_fiber_finlim
           {C : dfl_full_comp_cat}
           (Γ : C)
  : univ_cat_with_finlim.
Proof.
  use slice_univ_cat_with_finlim.
  - exact (dfl_full_comp_cat_to_finlim C).
  - exact Γ.
Defined.

Definition fiber_comp_cat_comprehension_functor_finlim
           {C : dfl_full_comp_cat}
           (Γ : C)
  : functor_finlim
      (dfl_full_comp_cat_fiber Γ)
      (dfl_full_comp_cat_to_cod_fiber_finlim Γ).
Proof.
  use (make_functor_finlim_adjequiv _).
  - exact (fiber_functor (comp_cat_comprehension C) Γ).
  - exact (fiber_functor_comprehension_adj_equiv C Γ).
Defined.

(** * 2. Preservation of initial objects *)
Definition preserves_initial_dfl_full_comp_cat_adjequiv_base_functor
           {C : dfl_full_comp_cat}
           (I : fiberwise_cat_property
                  strict_initial_local_property
                  C)
  : preserves_initial
      (dfl_full_comp_cat_adjequiv_base_functor C)
  := cat_property_adj_equivalence_of_cats'
       strict_initial_local_property
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base _)
       (I [])
       (local_property_in_dfl_comp_cat strict_initial_local_property C I).

(** * 3. Preservation of subobject classifiers *)
Definition preserves_subobj_classifier_dfl_full_comp_cat_adjequiv_base_functor
           {C : dfl_full_comp_cat}
           (Ω : fiberwise_cat_property
                  subobject_classifier_local_property
                  C)
  : preserves_subobject_classifier
      (dfl_full_comp_cat_adjequiv_base_functor C)
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_fiber []))
      (terminal_univ_cat_with_finlim (dfl_full_comp_cat_to_finlim C))
      (functor_finlim_preserves_terminal
         (dfl_full_comp_cat_adjequiv_base_functor_finlim C))
  := cat_property_adj_equivalence_of_cats'
       subobject_classifier_local_property
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base _)
       (Ω [])
       (local_property_in_dfl_comp_cat subobject_classifier_local_property C Ω).

(** * 4. Preservation of parameterized natural number objects *)
Definition preserves_pnno_dfl_full_comp_cat_adjequiv_base_functor
           {C : dfl_full_comp_cat}
           (N : fiberwise_cat_property
                  parameterized_NNO_local_property
                  C)
  : preserves_parameterized_NNO (N [])
      (local_property_in_dfl_comp_cat parameterized_NNO_local_property C N)
      (dfl_full_comp_cat_adjequiv_base_functor C)
      (functor_finlim_preserves_terminal
         (dfl_full_comp_cat_adjequiv_base_functor_finlim C))
  := cat_property_adj_equivalence_of_cats'
       parameterized_NNO_local_property
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base _)
       (N [])
       (local_property_in_dfl_comp_cat parameterized_NNO_local_property C N).

(** * 5. Preservation of binary coproducts *)
Definition preserves_bincoproduct_fiber_comp_cat_comprehension
           {C : dfl_full_comp_cat}
           (Γ : C)
  : preserves_bincoproduct (fiber_functor (comp_cat_comprehension C) Γ).
Proof.
  use left_adjoint_preserves_bincoproduct.
  apply (fiber_functor_comprehension_adj_equiv C Γ).
Qed.

Definition preserves_bincoproduct_fiber_comp_cat_comprehension_dom
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           (Γ : C)
  : preserves_bincoproduct
      (fiber_functor (comp_cat_comprehension C) Γ ∙ slice_dom Γ).
Proof.
  use composition_preserves_bincoproduct.
  - exact (preserves_bincoproduct_fiber_comp_cat_comprehension Γ).
  - refine (preserves_bincoproducts_slice_dom Γ _).
    exact (dfl_full_comp_cat_to_finlim_bincoproducts HC).
Qed.

Definition preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           {A₁ A₂ : ty Γ}
           (B₁ : BinCoproduct (C := fiber_category _ _) A₁ A₂)
           (B₂ : BinCoproduct (Γ & A₁) (Γ & A₂))
  : z_iso (Γ & BinCoproductObject B₁) B₂
  := preserves_bincoproduct_to_z_iso
       _
       (preserves_bincoproduct_fiber_comp_cat_comprehension_dom HC Γ)
       B₁ B₂.

Definition preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso_comm
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   C)
           {Γ : C}
           {A₁ A₂ : ty Γ}
           (B₁ : BinCoproduct (C := fiber_category _ _) A₁ A₂)
           (B₂ : BinCoproduct (Γ & A₁) (Γ & A₂))
  : inv_from_z_iso
      (preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso HC B₁ B₂)
    · π _
    =
    BinCoproductArrow _ (π A₁) (π A₂).
Proof.
  use BinCoproductArrowsEq.
  - rewrite BinCoproductIn1Commutes.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply BinCoproductIn1Commutes.
    }
    etrans.
    {
      exact (comprehension_functor_mor_comm
               (comp_cat_comprehension C)
               (BinCoproductIn1 B₁)).
    }
    apply id_right.
  - rewrite BinCoproductIn2Commutes.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply BinCoproductIn2Commutes.
    }
    etrans.
    {
      exact (comprehension_functor_mor_comm
               (comp_cat_comprehension C)
               (BinCoproductIn2 B₁)).
    }
    apply id_right.
Qed.

(** * 6. Preservation of truncations *)
Proposition preserves_regular_epi_comp_cat_comprehension
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            (Γ : C)
  : preserves_regular_epi (fiber_functor (comp_cat_comprehension C) Γ).
Proof.
  use (cat_property_adj_equivalence_of_cats'
         regular_local_property
         (fiber_comp_cat_comprehension_functor_finlim Γ)
         (fiber_functor_comprehension_adj_equiv C Γ)).
  - apply HC.
  - refine (local_property_slice
              regular_local_property
              _
              _
              _).
    apply local_property_in_dfl_comp_cat.
    exact HC.
Qed.

Definition comprehension_preserves_truncation_mor
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           (A : ty Γ)
  : (Γ & regular_local_property_trunc HC A)
    -->
    regular_category_im
      (regular_local_property_base_regular HC)
      (π A).
Proof.
  use (is_strong_epi_regular_epi_lift
         (from_regular_epi_in_slice
            (pr12 (regular_local_property_base_regular HC))
            (pr122 (regular_local_property_base_regular HC))
            (pr222 (regular_local_property_base_regular HC))
            (preserves_regular_epi_comp_cat_comprehension
               HC Γ _ _ _
               (is_regular_to_regular_local_property_trunc HC A)))
         (regular_category_im_Monic
            (regular_local_property_base_regular HC) (π A))
         (regular_category_to_im _ _)
         (π _)
         _
         (MonicisMonic _ _)).
  abstract
    (rewrite <- regular_category_im_commutes ;
     apply mor_eq).
Defined.

Definition comprehension_preserves_truncation_inv
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           (A : ty Γ)
  : regular_category_im
      (regular_local_property_base_regular HC)
      (π A)
    -->
    (Γ & regular_local_property_trunc HC A).
Proof.
  use (is_strong_epi_regular_epi_lift
         (is_regular_epi_regular_category_to_im
            (regular_local_property_base_regular HC)
            (π A))).
  - exact Γ.
  - exact (π _).
  - refine (dom_mor (#(fiber_functor (comp_cat_comprehension C) Γ) _)).
    apply to_regular_local_property_trunc.
  - apply regular_category_im_Monic.
  - abstract
      (refine (_ @ !(mor_eq _)) ;
       simpl ;
    exact (!(regular_category_im_commutes _ _))).
  - apply (hprop_ty_to_monic (is_hprop_ty_trunc HC A)).
Defined.

Proposition comprehension_preserves_truncation_inv_laws
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ : C}
            (A : ty Γ)
  : is_inverse_in_precat
      (comprehension_preserves_truncation_mor HC A)
      (comprehension_preserves_truncation_inv HC A).
Proof.
  split.
  - use (is_strong_epi_regular_epi_unique
           (from_regular_epi_in_slice
              (pr12 (regular_local_property_base_regular HC))
              (pr122 (regular_local_property_base_regular HC))
              (pr222 (regular_local_property_base_regular HC))
              (preserves_regular_epi_comp_cat_comprehension
                 HC Γ _ _ _
                 (is_regular_to_regular_local_property_trunc HC A)))).
    + exact Γ.
    + exact (π _).
    + refine (dom_mor (#(fiber_functor (comp_cat_comprehension C) Γ) _)).
      apply to_regular_local_property_trunc.
    + exact (π _).
    + apply idpath.
    + apply (hprop_ty_to_monic (is_hprop_ty_trunc HC A)).
    + rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply is_strong_epi_regular_epi_comm_left.
      }
      apply is_strong_epi_regular_epi_comm_left.
    + rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply is_strong_epi_regular_epi_comm_right.
      }
      apply is_strong_epi_regular_epi_comm_right.
    + apply id_left.
    + apply id_right.
  - use (regular_category_mor_to_im_eq _).
    + apply identity.
    + apply identity.
    + rewrite id_right, id_left.
      apply idpath.
    + rewrite !assoc'.
      rewrite id_right.
      etrans.
      {
        apply maponpaths.
        apply is_strong_epi_regular_epi_comm_left.
      }
      apply is_strong_epi_regular_epi_comm_left.
    + rewrite id_left, id_right.
      apply idpath.
    + rewrite id_left.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply is_strong_epi_regular_epi_comm_right.
      }
      apply is_strong_epi_regular_epi_comm_right.
    + rewrite id_left, id_right.
      apply idpath.
Qed.

Definition comprehension_preserves_truncation
           {C : dfl_full_comp_cat}
           (HC : fiberwise_cat_property regular_local_property C)
           {Γ : C}
           (A : ty Γ)
  : z_iso
      (Γ & regular_local_property_trunc HC A)
      (regular_category_im
         (regular_local_property_base_regular HC)
         (π A)).
Proof.
  use make_z_iso.
  - exact (comprehension_preserves_truncation_mor HC A).
  - exact (comprehension_preserves_truncation_inv HC A).
  - exact (comprehension_preserves_truncation_inv_laws HC A).
Defined.

Proposition comprehension_preserves_truncation_comm
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ : C}
            (A : ty Γ)
  : comprehension_preserves_truncation HC A
    · regular_epi_mono_factorization_mono _ _ _
    =
    π _.
Proof.
  apply is_strong_epi_regular_epi_comm_left.
Qed.

Proposition comprehension_preserves_truncation_inv_comm
            {C : dfl_full_comp_cat}
            (HC : fiberwise_cat_property regular_local_property C)
            {Γ : C}
            (A : ty Γ)
  : inv_from_z_iso (comprehension_preserves_truncation HC A)
    · π _
    =
    regular_epi_mono_factorization_mono _ _ _.
Proof.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply comprehension_preserves_truncation_comm.
  }
  rewrite !assoc.
  rewrite z_iso_after_z_iso_inv.
  apply id_left.
Qed.

(** * 7. Preservation of extensional identity types *)
Section PreservationExtIdComprehension.
  Context {C : dfl_full_comp_cat}.

  Section FiberEqualizer.
    Context {Γ : C}
            {A : ty Γ}
            (t₁ t₂ : tm Γ A)
            (e : Equalizer t₁ t₂).

    Definition comp_cat_fiber_equalizer_ob
      : C/Γ.
    Proof.
      use make_cod_fib_ob.
      - exact e.
      - exact (EqualizerArrow e).
    Defined.

    Definition comp_cat_fiber_equalizer_mor
      : comp_cat_fiber_equalizer_ob
        -->
        fiber_functor (comp_cat_comprehension C) Γ (dfl_full_comp_cat_unit Γ).
    Proof.
      use make_cod_fib_mor.
      - exact (EqualizerArrow e · inv_from_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)).
      - abstract
          (rewrite assoc' ;
           rewrite z_iso_after_z_iso_inv ;
           apply id_right).
    Defined.

    Lemma comp_cat_fiber_equalizer_eq_help
      : EqualizerArrow e
        · inv_from_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)
        · dom_mor ((♯(comp_cat_comprehension C))%mor_disp (dfl_full_comp_cat_tm_to_mor t₁))
        =
        EqualizerArrow e
        · inv_from_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)
        · dom_mor ((♯(comp_cat_comprehension C))%mor_disp (dfl_full_comp_cat_tm_to_mor t₂)).
    Proof.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (maponpaths pr1 (dfl_full_comp_cat_tm_to_mor_to_tm t₁)).
      }
      refine (EqualizerEqAr e @ _).
      refine (!_).
      apply maponpaths.
      exact (maponpaths pr1 (dfl_full_comp_cat_tm_to_mor_to_tm t₂)).
    Qed.

    Proposition comp_cat_fiber_equalizer_eq
      : comp_cat_fiber_equalizer_mor
        · #(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₁)
        =
        comp_cat_fiber_equalizer_mor
        · #(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₂).
    Proof.
      unfold comp_cat_fiber_equalizer_mor.
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      exact comp_cat_fiber_equalizer_eq_help.
    Qed.

    Section UMP.
      Context {x : C/Γ}
              (h : x --> fiber_functor (comp_cat_comprehension C) Γ (dfl_full_comp_cat_unit Γ))
              (p : h · #(fiber_functor (comp_cat_comprehension C) Γ)
                        (dfl_full_comp_cat_tm_to_mor t₁)
                   =
                   h · #(fiber_functor (comp_cat_comprehension C) Γ)
                        (dfl_full_comp_cat_tm_to_mor t₂)).

      Lemma to_comp_cat_fiber_equalizer_mor_dom_help
        : cod_mor x · t₁ = cod_mor x · t₂.
      Proof.
        rewrite <- (mor_eq h).
        refine (_ @ maponpaths dom_mor p @ _).
        - rewrite comp_in_cod_fib.
          cbn.
          rewrite !assoc'.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (maponpaths pr1 (dfl_full_comp_cat_tm_to_mor_to_tm t₁)).
          }
          simpl.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply (z_iso_inv_after_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)).
          }
          apply id_left.
        - rewrite comp_in_cod_fib.
          cbn.
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (maponpaths pr1 (dfl_full_comp_cat_tm_to_mor_to_tm t₂)).
          }
          simpl.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply (z_iso_inv_after_z_iso (dfl_full_comp_cat_extend_unit_z_iso Γ)).
          }
          apply id_left.
      Qed.

      Definition to_comp_cat_fiber_equalizer_mor_dom
        : cod_dom x --> cod_dom comp_cat_fiber_equalizer_ob.
      Proof.
        use EqualizerIn.
        - exact (cod_mor x).
        - exact to_comp_cat_fiber_equalizer_mor_dom_help.
      Defined.

      Definition to_comp_cat_fiber_equalizer_mor
        : x --> comp_cat_fiber_equalizer_ob.
      Proof.
        use make_cod_fib_mor.
        - exact to_comp_cat_fiber_equalizer_mor_dom.
        - abstract
            (apply EqualizerCommutes).
      Defined.

      Proposition to_comp_cat_fiber_equalizer_comm
        : to_comp_cat_fiber_equalizer_mor · comp_cat_fiber_equalizer_mor
          =
          h.
      Proof.
        use eq_mor_cod_fib.
        refine (comp_in_cod_fib _ _ @ _).
        cbn.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply EqualizerCommutes.
        }
        refine (!_).
        use z_iso_inv_on_left.
        exact (!(mor_eq h)).
      Qed.

      Proposition to_comp_cat_fiber_equalizer_unique
        : isaprop (∑ φ, φ · comp_cat_fiber_equalizer_mor = h).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use eq_mor_cod_fib.
        use EqualizerInsEq.
        use (cancel_z_iso _ _ (z_iso_inv (dfl_full_comp_cat_extend_unit_z_iso Γ))).
        rewrite !assoc'.
        pose (q := maponpaths dom_mor (pr2 ζ₁ @ !(pr2 ζ₂))).
        rewrite !comp_in_cod_fib in q.
        simpl in q.
        exact q.
      Qed.
    End UMP.

    Proposition comp_cat_fiber_equalizer_isEqualizer
      : isEqualizer
          (#(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₁))
          (#(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₂))
          comp_cat_fiber_equalizer_mor comp_cat_fiber_equalizer_eq.
    Proof.
      intros x h p.
      use iscontraprop1.
      - exact (to_comp_cat_fiber_equalizer_unique h).
      - simple refine (_ ,, _).
        + exact (to_comp_cat_fiber_equalizer_mor h p).
        + exact (to_comp_cat_fiber_equalizer_comm h p).
    Defined.

    Definition comp_cat_fiber_equalizer
      : Equalizer
          (#(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₁))
          (#(fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₂)).
    Proof.
      use make_Equalizer.
      - exact comp_cat_fiber_equalizer_ob.
      - exact comp_cat_fiber_equalizer_mor.
      - exact comp_cat_fiber_equalizer_eq.
      - exact comp_cat_fiber_equalizer_isEqualizer.
    Defined.
  End FiberEqualizer.

  Definition comprehension_preserves_ext_id_z_iso
             {Γ : C}
             {A : ty Γ}
             {t₁ t₂ : tm Γ A}
             (e : Equalizer t₁ t₂)
    : z_iso (Γ & dfl_ext_identity_type t₁ t₂) e
    := z_iso_to_cod_dom
         _ _ _
         (preserves_equalizer_z_iso
            _
            (preserves_equalizer_fiber_functor_comprehension C Γ)
            (dfl_ext_identity t₁ t₂)
            (comp_cat_fiber_equalizer t₁ t₂ e)).

  Proposition comprehension_preserves_ext_id_z_iso_comm
              {Γ : C}
              {A : ty Γ}
              (t₁ t₂ : tm Γ A)
              (e : Equalizer t₁ t₂)
    : comprehension_preserves_ext_id_z_iso e · EqualizerArrow e
      =
      cod_mor _.
  Proof.
    apply EqualizerCommutes.
  Qed.

  Proposition comprehension_preserves_ext_id_z_iso_inv_comm
              {Γ : C}
              {A : ty Γ}
              (t₁ t₂ : tm Γ A)
              (e : Equalizer t₁ t₂)
    : inv_from_z_iso (comprehension_preserves_ext_id_z_iso e) · cod_mor _
      =
      EqualizerArrow e.
  Proof.
    use z_iso_inv_on_right.
    rewrite comprehension_preserves_ext_id_z_iso_comm.
    apply idpath.
  Qed.
End PreservationExtIdComprehension.
