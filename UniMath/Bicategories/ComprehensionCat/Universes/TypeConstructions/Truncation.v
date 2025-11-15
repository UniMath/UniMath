(**

 Constructions of codes for propositional truncations in universes

 We have defined what it means for a universe in a category with finite limits and for a
 universe in a comprehension category to support propositional truncations. Our goal is to
 connect these two notions. To do so, we use the biequivalence between categories with finite
 limits and a universe and DFL full comprehension categories with a universe. Specifically, we
 showed that if `C` is a comprehension category with a universe `u`, then its category of
 contexts also has a universe. We construct an equivalence between the type that expresses that
 `C` supports propositional truncations and the type that the universe in the category of
 contexts supports propositional truncations.

 Contents
 1. Construction of truncations in the category of contexts
 2. Construction of truncations in a comprehension category
 3. The equivalence

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Truncation.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Truncation.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Section TruncationUniverse.
  Context {C : dfl_full_comp_cat_with_univ}
          (tr : fiberwise_cat_property
                  regular_local_property
                  (dfl_full_comp_cat_with_univ_types C)).

  (** * 1. Construction of truncations in the category of contexts *)
  Definition truncation_in_dfl_full_comp_cat_to_finlim_univ_code
             (trc : stable_truncation_in_comp_cat_univ C tr)
             {Γ : C}
             (a : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : Γ --> [] & dfl_full_comp_cat_univ_ob C.
  Proof.
    use (dfl_full_comp_cat_tm_to_mor_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    refine (truncation_in_comp_cat_univ_code tr trc _).
    use (dfl_full_comp_cat_mor_to_tm_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    exact a.
  Defined.

  Arguments truncation_in_dfl_full_comp_cat_to_finlim_univ_code /.

  Definition truncation_in_dfl_full_comp_cat_to_finlim_univ_z_iso
             (trc : stable_truncation_in_comp_cat_univ C tr)
             {Γ : C}
             (a : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : z_iso
        (cat_el_map_el
           (dfl_full_comp_cat_to_finlim_el_map
              (dfl_full_comp_cat_univ_ob C)
              (dfl_full_comp_cat_el C))
           (truncation_in_dfl_full_comp_cat_to_finlim_univ_code trc a))
        (regular_category_im
           (regular_local_property_base_regular tr)
           (cat_el_map_mor
              (dfl_full_comp_cat_to_finlim_el_map
                 (dfl_full_comp_cat_univ_ob C)
                 (dfl_full_comp_cat_el C))
              a)).
  Proof.
    refine (z_iso_comp
              (z_iso_comp _ (truncation_in_comp_cat_univ_z_iso _ trc _)) _).
    - use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
      apply (dfl_full_comp_cat_tm_to_mor_to_tm_univ
               (dfl_full_comp_cat_univ_ob C)).
    - exact (comprehension_preserves_truncation tr _).
  Defined.

  Proposition truncation_in_dfl_full_comp_cat_to_finlim_univ_comm
              (trc : stable_truncation_in_comp_cat_univ C tr)
              {Γ : C}
              (a : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : truncation_in_dfl_full_comp_cat_to_finlim_univ_z_iso trc a
      · regular_epi_mono_factorization_mono
          (is_regular_category_pullbacks (regular_local_property_base_regular tr))
          (is_regular_category_coeqs_of_kernel_pair (regular_local_property_base_regular tr))
          (cat_el_map_mor
             (dfl_full_comp_cat_to_finlim_el_map (dfl_full_comp_cat_univ_ob C)
                (dfl_full_comp_cat_el C))
             a)
      =
      cat_el_map_mor
        (dfl_full_comp_cat_to_finlim_el_map
           (dfl_full_comp_cat_univ_ob C)
           (dfl_full_comp_cat_el C))
        (truncation_in_dfl_full_comp_cat_to_finlim_univ_code trc a).
  Proof.
    unfold truncation_in_dfl_full_comp_cat_to_finlim_univ_z_iso.
    do 2 refine (assoc' _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      exact (comprehension_preserves_truncation_comm _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (truncation_in_comp_cat_univ_comm tr trc _).
    }
    etrans.
    {
      apply comprehension_functor_mor_comm.
    }
    apply id_right.
  Qed.

  Definition truncation_in_dfl_full_comp_cat_to_finlim_univ
             (trc : stable_truncation_in_comp_cat_univ C tr)
    : cat_univ_codes_trunc
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (regular_local_property_base_regular tr).
  Proof.
    use make_cat_univ_codes_trunc.
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_to_finlim_univ_code trc a).
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_to_finlim_univ_z_iso trc a).
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_to_finlim_univ_comm trc a).
  Defined.

  Proposition is_stable_truncation_in_dfl_full_comp_cat_to_finlim_univ
              (trc : stable_truncation_in_comp_cat_univ C tr)
    : is_stable_cat_univ_trunc
        (truncation_in_dfl_full_comp_cat_to_finlim_univ trc).
  Proof.
    intros Γ Δ s a ; cbn.
    refine (assoc _ _ _ @ _).
    etrans.
    {
      exact (stable_truncation_in_comp_cat_univ_code_stable_mor C _ trc s _).
    }
    refine (maponpaths (λ z, z · _) _).
    use truncation_in_comp_cat_univ_code_eq.
    exact (dfl_full_comp_cat_mor_to_sub_tm (dfl_full_comp_cat_univ_ob C) s a).
  Qed.

  Definition stable_truncation_in_dfl_full_comp_cat_to_finlim_univ
             (trc : stable_truncation_in_comp_cat_univ C tr)
    : cat_univ_stable_codes_trunc
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (regular_local_property_base_regular tr).
  Proof.
    use make_cat_univ_stable_codes_trunc.
    - exact (truncation_in_dfl_full_comp_cat_to_finlim_univ trc).
    - exact (is_stable_truncation_in_dfl_full_comp_cat_to_finlim_univ trc).
  Defined.

  (** * 2. Construction of truncations in a comprehension category *)
  Definition truncation_in_dfl_full_comp_cat_from_finlim_univ_code
             (trc : cat_univ_stable_codes_trunc
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (regular_local_property_base_regular tr))
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
    : tm Γ (dfl_full_comp_cat_univ Γ).
  Proof.
    use (dfl_full_comp_cat_mor_to_tm_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    use (cat_univ_trunc_code trc).
    use (dfl_full_comp_cat_tm_to_mor_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    exact a.
  Defined.

  Arguments truncation_in_dfl_full_comp_cat_from_finlim_univ_code /.

  Definition truncation_in_dfl_full_comp_cat_from_finlim_univ_z_iso
             (trc : cat_univ_stable_codes_trunc
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (regular_local_property_base_regular tr))
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
    : z_iso
        (Γ & comp_cat_univ_el
               (dfl_full_comp_cat_el C)
               (truncation_in_dfl_full_comp_cat_from_finlim_univ_code trc a))
        (Γ & regular_local_property_trunc
               tr
               (comp_cat_univ_el (dfl_full_comp_cat_el C) a)).
  Proof.
    refine (z_iso_comp
              (cat_univ_trunc_z_iso
                 trc
                 _)
              _).
    use z_iso_inv.
    refine (z_iso_comp
              (comprehension_preserves_truncation tr _)
              _).
    use regular_category_im_eq_triangle_z_iso.
    - use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
      abstract
        (rewrite dfl_full_comp_cat_tm_to_mor_to_tm_univ ;
         apply idpath).
    - abstract
        (refine (!_) ;
         refine (comprehension_functor_mor_comm _ _ @ _) ;
         apply id_right).
  Defined.

  Proposition truncation_in_dfl_full_comp_cat_from_finlim_univ_comm
              (trc : cat_univ_stable_codes_trunc
                       (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                       (regular_local_property_base_regular tr))
              {Γ : C}
              (a : tm Γ (dfl_full_comp_cat_univ Γ))
    : truncation_in_dfl_full_comp_cat_from_finlim_univ_z_iso trc a · π _
      =
      π _.
  Proof.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (comprehension_preserves_truncation_inv_comm tr _).
    }
    etrans.
    {
      apply maponpaths.
      apply regular_category_im_map_left.
    }
    rewrite id_right.
    exact (cat_univ_trunc_comm trc _).
  Qed.

  Definition truncation_in_dfl_full_comp_cat_from_finlim_univ
             (trc : cat_univ_stable_codes_trunc
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (regular_local_property_base_regular tr))
    : truncation_in_comp_cat_univ C tr.
  Proof.
    use make_truncation_in_comp_cat_univ.
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_from_finlim_univ_code trc a).
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_from_finlim_univ_z_iso trc a).
    - exact (λ Γ a, truncation_in_dfl_full_comp_cat_from_finlim_univ_comm trc a).
  Defined.

  Proposition is_stable_truncation_in_dfl_full_comp_cat_from_finlim_univ
              (trc : cat_univ_stable_codes_trunc
                       (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                       (regular_local_property_base_regular tr))
    : trunc_in_comp_cat_univ_is_stable
        C tr
        (truncation_in_dfl_full_comp_cat_from_finlim_univ trc).
  Proof.
    intros Γ Δ s a.
    use dfl_full_comp_cat_univ_tm_eq ; simpl.
    etrans.
    {
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      simpl.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    refine (cat_univ_stable_codes_trunc_stable trc s _ @ _).
    refine (!_).
    etrans.
    {
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    apply maponpaths.
    exact (dfl_full_comp_cat_tm_to_mor_univ_subst s a).
  Qed.

  Definition stable_truncation_in_dfl_full_comp_cat_from_finlim_univ
             (trc : cat_univ_stable_codes_trunc
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (regular_local_property_base_regular tr))
    : stable_truncation_in_comp_cat_univ C tr.
  Proof.
    use make_stable_truncation_in_comp_cat_univ.
    - exact (truncation_in_dfl_full_comp_cat_from_finlim_univ trc).
    - exact (is_stable_truncation_in_dfl_full_comp_cat_from_finlim_univ trc).
  Defined.

  (** * 3. The equivalence *)
  Definition stable_truncation_in_dfl_full_comp_cat_weq_finlim_univ
    : stable_truncation_in_comp_cat_univ C tr
      ≃
      cat_univ_stable_codes_trunc
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (regular_local_property_base_regular tr).
  Proof.
    use weq_iso.
    - exact stable_truncation_in_dfl_full_comp_cat_to_finlim_univ.
    - exact stable_truncation_in_dfl_full_comp_cat_from_finlim_univ.
    - abstract
        (intro trc ;
         use stable_truncation_in_comp_cat_univ_eq ;
         intros Γ a ; cbn ;
         refine (dfl_full_comp_cat_tm_to_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) _
                 @ _) ;
         apply maponpaths ;
         exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) _)).
    - abstract
        (intro trc ;
         use cat_univ_stable_codes_trunc_eq ;
         intros Γ a ; cbn ;
         refine (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _
                 @ _) ;
         apply maponpaths ;
         exact (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _)).
  Defined.
End TruncationUniverse.
