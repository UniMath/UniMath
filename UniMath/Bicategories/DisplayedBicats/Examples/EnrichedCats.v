Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Enriched.Enrichment.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor.

Section EnrichedMors.
  Context (V : monoidal_cat).

  Definition disp_cat_ob_mor_of_enriched_cats
    : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (C : univalent_category), enrichment C V).
    - exact (λ (C₁ C₂ : univalent_category)
               (E₁ : enrichment C₁ V)
               (E₂ : enrichment C₂ V)
               (F : C₁ ⟶ C₂),
             functor_enrichment F E₁ E₂).
  Defined.

  Definition disp_cat_id_comp_of_enriched_cats
    : disp_cat_id_comp bicat_of_univ_cats disp_cat_ob_mor_of_enriched_cats.
  Proof.
    simple refine (_ ,, _).
    - exact (λ C E, functor_id_enrichment E).
    - exact (λ C₁ C₂ C₃ F G E₁ E₂ E₃ EF EG, functor_comp_enrichment EF EG).
  Defined.

  Definition disp_cat_data_of_enriched_cats
    : disp_cat_data bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_ob_mor_of_enriched_cats.
    - exact disp_cat_id_comp_of_enriched_cats.
  Defined.

  Definition disp_prebicat_1_id_comp_cells_of_enriched_cats
    : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_data_of_enriched_cats.
    - exact (λ C₁ C₂ F G τ E₁ E₂ EF EG, nat_trans_enrichment τ EF EG).
  Defined.

  Definition disp_prebicat_ops_of_enriched_cats
    : disp_prebicat_ops disp_prebicat_1_id_comp_cells_of_enriched_cats.
  Proof.
    repeat split ; cbn.
    - exact (λ C₁ C₂ F E₁ E₂ FE, id_trans_enrichment FE).
    - exact (λ C₁ C₂ F E₁ E₂ FE, lunitor_enrichment FE).
    - exact (λ C₁ C₂ F E₁ E₂ FE, runitor_enrichment FE).
    - exact (λ C₁ C₂ F E₁ E₂ FE, linvunitor_enrichment FE).
    - exact (λ C₁ C₂ F E₁ E₂ FE, rinvunitor_enrichment FE).
    - exact (λ C₁ C₂ C₃ C₄ F G H E₁ E₂ E₃ E₄ FE GE HE,
             lassociator_enrichment FE GE HE).
    - exact (λ C₁ C₂ C₃ C₄ F G H E₁ E₂ E₃ E₄ FE GE HE,
             rassociator_enrichment FE GE HE).
    - exact (λ C₁ C₂ F G H τ τ' E₁ E₂ EF EG EH Eτ Eτ', comp_trans_enrichment Eτ Eτ').
    - exact (λ C₁ C₂ C₃ F G₁ G₂ τ E₁ E₂ E₃ EF EG₁ EG₂ Eτ, pre_whisker_enrichment EF Eτ).
    - exact (λ C₁ C₂ C₃ F₁ F₂ G τ E₁ E₂ E₃ EF₁ EF₂ EG Eτ, post_whisker_enrichment Eτ EG).
  Qed.

  Definition disp_prebicat_data_of_enriched_cats
    : disp_prebicat_data bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_1_id_comp_cells_of_enriched_cats.
    - exact disp_prebicat_ops_of_enriched_cats.
  Defined.

  Definition disp_prebicat_laws_of_enriched_cats
    : disp_prebicat_laws disp_prebicat_data_of_enriched_cats.
  Proof.
    repeat split ; intro ; intros ; cbn ; apply isaprop_nat_trans_enrichment.
  Qed.

  Definition disp_prebicat_of_enriched_cats
    : disp_prebicat bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_data_of_enriched_cats.
    - exact disp_prebicat_laws_of_enriched_cats.
  Defined.

  Definition disp_bicat_of_enriched_cats
    : disp_bicat bicat_of_univ_cats.
  Proof.
    simple refine (_ ,, _).
    - exact disp_prebicat_of_enriched_cats.
    - intros C₁ C₂ F G τ E₁ E₂ EF EG.
      apply isasetaprop.
      apply isaprop_nat_trans_enrichment.
  Defined.

  Definition disp_2cell_isapprop_enriched_cats
    : disp_2cells_isaprop disp_bicat_of_enriched_cats.
  Proof.
    intros C₁ C₂ F G τ E₁ E₂ EF EG.
    apply isaprop_nat_trans_enrichment.
  Qed.

  Definition disp_locally_sym_enriched_cats
    : disp_locally_sym disp_bicat_of_enriched_cats.
  Proof.
    intros C₁ C₂ F G τ E₁ E₂ FE GE τE x y ; cbn in *.
    pose ( p := τE x y).
  Admitted.

  Definition disp_locally_groupoid_enriched_cats
    : disp_locally_groupoid disp_bicat_of_enriched_cats.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_enriched_cats.
    - exact disp_2cell_isapprop_enriched_cats.
  Defined.

  Definition disp_univalent_2_1_enriched_cats
    : disp_univalent_2_1 disp_bicat_of_enriched_cats.
  Proof.
    intros C₁ C₂ F G p E₁ E₂ FE GE.
    induction p.
    use isweqimplimpl.
    - cbn in * ; intro τ.
      use subtypePath.
      {
        intro.
        apply isaprop_is_functor_enrichment.
      }
      use funextsec ; intro x.
      use funextsec ; intro y.
      pose (p := pr1 τ x y).
      cbn in p.
      rewrite !enriched_from_arr_id in p.
      refine (_ @ !p @ _) ; clear p.
      + rewrite <- !(functor_enrichment_id FE).
        rewrite (tensor_comp_r_id_l _ _ (FE x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp FE).
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          exact (enrichment_id_left E₁ x y).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_linvunitor_lunitor.
        }
        apply id_left.
      + rewrite <- !(functor_enrichment_id GE).
        rewrite (tensor_comp_l_id_l (GE x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp GE).
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          exact (enrichment_id_right E₁ x y).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
    - apply isaset_functor_enrichment.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
      + intros.
        apply isaprop_nat_trans_enrichment.
  Qed.
