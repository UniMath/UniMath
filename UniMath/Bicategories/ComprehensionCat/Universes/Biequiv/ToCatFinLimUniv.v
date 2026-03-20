(**

 Universes in category of contexts of a comprehension category

 In this file, we construct the displayed pseudofunctor that assigns to every comprehension
 category with a universe a category with a universe. The components of this displayed
 pseudofunctor are split into several files. In this file, we put everything together, and
 we construct the desired displayed pseudofunctor.

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Export UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivComp.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.
Local Open Scope comp_cat.

Definition dfl_comp_cat_to_finlim_disp_psfunctor_universe
  : disp_psfunctor
      disp_bicat_dfl_full_comp_cat_with_univ
      disp_bicat_finlim_universe
      dfl_comp_cat_to_finlim_psfunctor.
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_disp_bicat_finlim_universe.
  - exact disp_locally_groupoid_disp_bicat_finlim_universe.
  - intros C u.
    exact (dfl_full_comp_cat_to_finlim_ob (pr1 u)
           ,,
           dfl_full_comp_cat_to_finlim_stable_el_map_coherent (pr1 u) (pr2 u)).
  - intros C₁ C₂ F u₁ u₂ Fu.
    exact (dfl_full_comp_cat_functor_preserves_ob F (pr1 Fu)
           ,,
           dfl_full_comp_cat_functor_preserves_el F (pr1 Fu) (pr2 Fu)).
  - intros C₁ C₂ F G τ u₁ u₂ Fu₁ Gu₂ τu.
    simple refine (_ ,, _).
    + exact (dfl_full_comp_cat_to_nat_trans_ob τ (pr1 τu)).
    + exact (dfl_full_comp_cat_to_nat_trans_preserves_el τ (pr1 τu) (pr2 τu)).
  - intros C u.
    simple refine (_ ,, _).
    + exact (dfl_functor_comp_cat_to_finlim_univ_identitor_ob (pr1 u) _).
    + exact (dfl_functor_comp_cat_to_finlim_univ_identitor_preserves_el (pr1 u) (pr2 u)).
  - intros C₁ C₂ C₃ F G u₁ u₂ u₃ Fu Gu.
    simple refine (_ ,, _).
    + exact (dfl_functor_comp_cat_to_finlim_univ_compositor_ob (pr1 Fu) (pr1 Gu)).
    + exact (dfl_functor_comp_cat_to_finlim_univ_compositor_preserves_el
               (pr1 Fu) (pr1 Gu)
               (pr2 Fu) (pr2 Gu)).
Defined.
