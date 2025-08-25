Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
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
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
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
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.

Local Open Scope cat.
Local Open Scope comp_cat.

Definition dfl_full_comp_cat_adjequiv_base_functor
           (C : dfl_full_comp_cat)
  : dfl_full_comp_cat_fiber ([] : C) ⟶ dfl_full_comp_cat_to_finlim C
  := fiber_functor (comp_cat_comprehension C) []
     ∙ cod_fib_terminal_to_base _.

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
         (make_functor_finlim_adjequiv (dfl_full_comp_cat_adjequiv_base_functor C)
            (dfl_full_comp_cat_adjequiv_base C)))
  := cat_property_adj_equivalence_of_cats'
       subobject_classifier_local_property
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base _)
       (Ω [])
       (local_property_in_dfl_comp_cat subobject_classifier_local_property C Ω).

Definition preserves_pnno_dfl_full_comp_cat_adjequiv_base_functor
           {C : dfl_full_comp_cat}
           (N : fiberwise_cat_property
                  parameterized_NNO_local_property
                  C)
  : preserves_parameterized_NNO (N [])
      (local_property_in_dfl_comp_cat parameterized_NNO_local_property C N)
      (dfl_full_comp_cat_adjequiv_base_functor C)
      (functor_finlim_preserves_terminal
         (make_functor_finlim_adjequiv
            (dfl_full_comp_cat_adjequiv_base_functor C)
            (dfl_full_comp_cat_adjequiv_base C)))
  := cat_property_adj_equivalence_of_cats'
       parameterized_NNO_local_property
       (dfl_full_comp_cat_adjequiv_base_functor C)
       (dfl_full_comp_cat_adjequiv_base _)
       (N [])
       (local_property_in_dfl_comp_cat parameterized_NNO_local_property C N).



Section PreservationComprehension.
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
          (# (fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₁))
          (# (fiber_functor (comp_cat_comprehension C) Γ) (dfl_full_comp_cat_tm_to_mor t₂)).
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
End PreservationComprehension.
