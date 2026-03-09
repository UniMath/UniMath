(**

 From comprehension categories with a universe to categories with a universe

 Our goal is to define a pseudofunctor from the bicategory of (DFL, full, univalent)
 comprehension categories with a universe to the bicategory of univalent categories with
 finite limits and a universe. This is one of the necessary ingredients to extend the
 biequivalence between DFL full comprehension categories and categories with finite limits
 to universes. This pseudofunctor is constructed as a displayed pseudofunctor over the
 pseudofunctor that assigned to every comprehension category its category of context.

 This file defines the actions on 2-cells of the desired pseudofunctor. The construction
 has been split up so that the resulting files are smaller and so that they can be compiled
 concurrently. The action on 2-cells is constructed by verifying two axioms.

 Contents
 1. Coherence for the universe
 2. Coherence for the associated types map

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.
Local Open Scope comp_cat.

Section ToNatTransFinLimUniv.
  Context {C₁ C₂ : dfl_full_comp_cat}
          {F G : dfl_full_comp_cat_functor C₁ C₂}
          (τ : dfl_full_comp_cat_nat_trans F G)
          {u₁ : ty ([] : C₁)}
          {u₂ : ty ([] : C₂)}.

  Let Cu₁ : comp_cat_with_ob := pr11 C₁ ,, u₁.
  Let Cu₂ : comp_cat_with_ob := pr11 C₂ ,, u₂.
  Let CCu₁ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₁ ,, dfl_full_comp_cat_to_finlim_ob u₁.
  Let CCu₂ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₂ ,, dfl_full_comp_cat_to_finlim_ob u₂.

  Context {el₁ : comp_cat_univ_type Cu₁}
          {el₂ : comp_cat_univ_type Cu₂}
          {F_u : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso F)
                  (comp_cat_type_functor F [] u₁)
                  u₂}
          {G_u : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso G)
                  (comp_cat_type_functor G [] u₁)
                  u₂}.

  Let Fu : comp_cat_functor_ob Cu₁ Cu₂ := pr11 F ,, F_u.
  Let Gu : comp_cat_functor_ob Cu₁ Cu₂ := pr11 G ,, G_u.

  Let FFu : functor_finlim_ob CCu₁ CCu₂
    := dfl_functor_comp_cat_to_finlim_functor F
       ,,
       dfl_full_comp_cat_functor_preserves_ob F F_u.
  Let GGu : functor_finlim_ob CCu₁ CCu₂
    := dfl_functor_comp_cat_to_finlim_functor G
       ,,
       dfl_full_comp_cat_functor_preserves_ob G G_u.

  Context {Fel : comp_cat_functor_preserves_univ_type Fu el₁ el₂}
          {Gel : comp_cat_functor_preserves_univ_type Gu el₁ el₂}
          (p : pr2 Fu ==>[ pr11 τ ] pr2 Gu).

  Let τu : comp_cat_nat_trans_ob Fu Gu := pr11 τ ,, p.

  Context (τel : comp_cat_nat_trans_preserves_univ_type τu Fel Gel).

  (** * 1. Coherence for the universe *)
  Proposition dfl_full_comp_cat_to_nat_trans_ob
    : τ (dfl_full_comp_cat_to_finlim_ob u₁)
      · (comprehension_nat_trans_mor (comp_cat_functor_comprehension G) u₁
      · comprehension_functor_mor (comp_cat_comprehension C₂) G_u)
      =
      comprehension_nat_trans_mor (comp_cat_functor_comprehension F) u₁
      · comprehension_functor_mor (comp_cat_comprehension C₂) F_u.
  Proof.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (!p).
    }
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply comp_cat_nat_trans_comprehension.
  Qed.

  Let ττu : nat_trans_finlim_ob FFu GGu
    := psfunctor_on_cells dfl_comp_cat_to_finlim_psfunctor τ
       ,,
       dfl_full_comp_cat_to_nat_trans_ob.

  (** * 2. Coherence for the associated types map *)
  Proposition dfl_full_comp_cat_to_nat_trans_preserves_el
    : nat_trans_preserves_el
        ττu
        (dfl_full_comp_cat_functor_preserves_el F _ Fel)
        (dfl_full_comp_cat_functor_preserves_el G _ Gel).
  Proof.
    intros Γ t.
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!_).
      apply comp_cat_nat_trans_comprehension.
    }
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!(comprehension_functor_mor_comp _ _ _) @ _).
      simpl.
      apply idpath.
    }
    refine (!_).
    do 2 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply dfl_full_comp_cat_cat_el_map_el_eq.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply comprehension_functor_mor_transportf.
      }
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      apply maponpaths_2.
      apply comprehension_functor_mor_transportf.
    }
    refine (!(comprehension_functor_mor_comp _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply (comp_cat_nat_trans_preserves_univ_type_alt τel).
    }
    etrans.
    {
      etrans ; [ apply maponpaths ; apply assoc_disp_var | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply mor_disp_transportf_postwhisker | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply assoc_disp_var | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply mor_disp_transportf_postwhisker | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply assoc_disp_var | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply mor_disp_transportf_postwhisker | ].
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans ; [ apply maponpaths ; apply assoc_disp_var | ].
      apply comprehension_functor_mor_transportf.
    }
    refine (!_).
    etrans.
    {
      etrans ; [ apply maponpaths ; apply mor_disp_transportf_prewhisker | ].
      apply comprehension_functor_mor_transportf.
    }
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      apply idpath.
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        do 4 apply maponpaths_2.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      rewrite !mor_disp_transportf_postwhisker.
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths_2.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      rewrite !mor_disp_transportf_postwhisker.
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      rewrite !mor_disp_transportf_postwhisker.
      apply idpath.
    }
    rewrite !transport_f_f.
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      apply idpath.
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths.
      do 2 apply maponpaths_2.
      use (comp_cat_univ_el_stable_natural_disp_alt el₂).
      exact (dfl_full_comp_cat_functor_preserves_el_map_eq G G_u t).
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      refine (assoc_disp_var _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        exact (inv_mor_after_z_iso_disp
                 (z_iso_disp_from_z_iso_fiber
                    _ _ _ _
                    (comp_cat_univ_el_stable el₂ (ττu Γ) _))).
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    rewrite id_right_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc_disp _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply cartesian_factorisation_commutes.
      }
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    rewrite !assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite !comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply cartesian_factorisation_commutes.
    }
    rewrite !mor_disp_transportf_postwhisker.
    rewrite comprehension_functor_mor_transportf.
    apply idpath.
  Qed.
End ToNatTransFinLimUniv.
