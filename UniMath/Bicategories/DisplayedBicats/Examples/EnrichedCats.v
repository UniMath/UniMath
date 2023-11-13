(*****************************************************************

 The bicategory of univalent enriched categories

 We construct the bicategory of univalent enriched categories and
 we prove that this bicategory is univalent. Note that in order to
 prove the univalence, it is sufficient to assume that the
 involved monoidal category is univalent as well.

 To define this bicategory, we use displayed bicategories. The
 base bicategory is the bicategory of univalent categories. Note
 that we cannot split this displayed bicategory into smaller
 parts. That is because to define natural transformations, we
 need to use composition of enriched categories.

 Note that the construction of the bicategories of enriched
 categories as a displayed bicategory, provides some explanation
 of what the notion of enrichment means. With the usual definition
 of enriched category, one has a pseudofunctor `V-Cat -> Cat`,
 which sends every enriched category to its underlying category.
 The projection pseudofunctor of the displayed bicategory defined
 in this file, is precisely this pseudofunctor. The notion of
 enrichment given in `Enrichment.v` represents the fibers of the
 underlying category pseudofunctor.

 Contents
 1. The displayed bicategory
 2. Local univalence
 3. Global univalence
 4. Accessors for the bicategory of enriched categories

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor.

Section EnrichedCats.
  Context (V : monoidal_cat).

  (** * 1. The displayed bicategory *)
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
    - exact (λ C₁ C₂ F G τ E₁ E₂ EF EG, nat_trans_enrichment (pr1 τ) EF EG).
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

  Proposition disp_locally_sym_enriched_cats
    : disp_locally_sym disp_bicat_of_enriched_cats.
  Proof.
    intros C₁ C₂ F G τ E₁ E₂ EF EG Eτ.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    refine (!(id_right _) @ _).
    rewrite <- postcomp_arr_id.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(maponpaths (λ z, pr1 z y) (vcomp_rinv τ))).
    }
    cbn.
    rewrite postcomp_arr_comp.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite precomp_postcomp_arr.
    cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (!nat_trans_enrichment_to_comp Eτ x y).
    }
    rewrite !assoc'.
    rewrite <- precomp_arr_comp.
    etrans.
    {
      do 2 apply maponpaths.
      exact (maponpaths (λ z, pr1 z x) (vcomp_linv τ)).
    }
    cbn.
    rewrite precomp_arr_id.
    apply id_right.
  Qed.

  Proposition disp_locally_groupoid_enriched_cats
    : disp_locally_groupoid disp_bicat_of_enriched_cats.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_locally_sym_enriched_cats.
    - exact disp_2cell_isapprop_enriched_cats.
  Qed.

  (** * 2. Local univalence *)
  Definition disp_univalent_2_1_enriched_cats
    : disp_univalent_2_1 disp_bicat_of_enriched_cats.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros C F G E₁ E₂ FE GE.
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

  (** * 3. Global univalence *)
  Section DispAdjointEquivalence.
    Context {C : bicat_of_univ_cats}
            (E₁ E₂ : disp_bicat_of_enriched_cats C).

    Definition make_disp_adjequiv_enriched
               (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
               (F₂ : functor_enrichment (functor_identity _) E₂ E₁)
               (η : nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_id_enrichment E₁)
                      (functor_comp_enrichment F₁ F₂))
               (ηinv : nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_comp_enrichment F₁ F₂)
                      (functor_id_enrichment E₁))
               (ε : nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_comp_enrichment F₂ F₁)
                      (functor_id_enrichment E₂))
               (εinv : nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_id_enrichment E₂)
                      (functor_comp_enrichment F₂ F₁))
      : disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity C)
          E₁ E₂.
    Proof.
      simple refine (F₁ ,, (F₂ ,, (η ,, ε)) ,, (_ ,, _)).
      - abstract
          (split ; apply disp_2cell_isapprop_enriched_cats).
      - split.
        + refine (ηinv ,, _ ,,  _) ; apply disp_2cell_isapprop_enriched_cats.
        + refine (εinv ,, _ ,,  _) ; apply disp_2cell_isapprop_enriched_cats.
    Defined.

    Definition from_disp_adjequiv_enriched
               (F : disp_adjoint_equivalence
                      (internal_adjoint_equivalence_identity C)
                      E₁ E₂)
      : ∑ (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
          (F₂ : functor_enrichment (functor_identity _) E₂ E₁),
        (nat_trans_enrichment
           (nat_trans_id _)
           (functor_id_enrichment E₁)
           (functor_comp_enrichment F₁ F₂))
        ×
        (nat_trans_enrichment
           (nat_trans_id _)
           (functor_comp_enrichment F₂ F₁)
           (functor_id_enrichment E₂))
        ×
        (nat_trans_enrichment
           (nat_trans_id _)
           (functor_comp_enrichment F₁ F₂)
           (functor_id_enrichment E₁))
        ×
        (nat_trans_enrichment
           (nat_trans_id _)
           (functor_id_enrichment E₂)
           (functor_comp_enrichment F₂ F₁)).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _).
      - exact (pr1 F).
      - exact (pr112 F).
      - exact (pr1 (pr212 F)).
      - exact (pr2 (pr212 F)).
      - exact (pr11 (pr222 F)).
      - exact (pr12 (pr222 F)).
    Defined.

    Definition weq_disp_adjequiv_enriched
      : (∑ (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
           (F₂ : functor_enrichment (functor_identity _) E₂ E₁),
         (nat_trans_enrichment
            (nat_trans_id _)
            (functor_id_enrichment E₁)
            (functor_comp_enrichment F₁ F₂))
         ×
         (nat_trans_enrichment
            (nat_trans_id _)
            (functor_comp_enrichment F₂ F₁)
            (functor_id_enrichment E₂))
         ×
         (nat_trans_enrichment
            (nat_trans_id _)
            (functor_comp_enrichment F₁ F₂)
            (functor_id_enrichment E₁))
         ×
         (nat_trans_enrichment
            (nat_trans_id _)
            (functor_id_enrichment E₂)
            (functor_comp_enrichment F₂ F₁)))
        ≃
        disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity C)
          E₁ E₂.
    Proof.
      use weq_iso.
      - exact (λ F,
               make_disp_adjequiv_enriched
                 (pr1 F)
                 (pr12 F) (pr122 F)
                 (pr12 (pr222 F))
                 (pr1 (pr222 F))
                 (pr22 (pr222 F))).
      - exact from_disp_adjequiv_enriched.
      - intros F.
        apply idpath.
      - abstract
          (intro F ;
           refine (maponpaths (λ z, _ ,, z) _) ;
           refine (maponpaths (λ z, _ ,, z) _) ;
           repeat (apply isapropdirprod) ;
           try (apply isaprop_is_disp_invertible_2cell) ;
           apply disp_bicat_of_enriched_cats).
    Defined.
  End DispAdjointEquivalence.

  Section FromEnrichmentPath.
    Context {C : bicat_of_univ_cats}
            {E₁ E₂ : disp_bicat_of_enriched_cats C}
            (F : enrichment_data_hom_path_help (pr1 E₁) (pr1 E₂)).

    Definition from_enrichment_path_functor_data
      : functor_enrichment_data (functor_identity _) E₁ E₂
      := λ x y, pr1 F x y.

    Definition from_enrichment_path_functor_is_functor
      : is_functor_enrichment from_enrichment_path_functor_data.
    Proof.
      repeat split.
      - intro x.
        exact (pr12 F x).
      - intros x y z.
        exact (pr122 F x y z).
      - intros x y f.
        exact (!(pr1 (pr222 F) x y f)).
    Qed.

    Definition from_enrichment_path_functor
      : functor_enrichment (functor_identity _) E₁ E₂
      := from_enrichment_path_functor_data
         ,,
         from_enrichment_path_functor_is_functor.

    Definition from_enrichment_path_functor_inv_data
      : functor_enrichment_data (functor_identity _) E₂ E₁
      := λ x y, inv_from_z_iso (pr1 F x y).

    Definition from_enrichment_path_functor_inv_is_functor
      : is_functor_enrichment from_enrichment_path_functor_inv_data.
    Proof.
      repeat split.
      - intros x.
        cbn ; unfold from_enrichment_path_functor_inv_data.
        refine (!_).
        use z_iso_inv_on_left.
        refine (!_).
        exact (pr12 F x).
      - intros x y z.
        cbn ; unfold from_enrichment_path_functor_inv_data.
        refine (!_).
        use z_iso_inv_on_left.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (pr122 F x y z).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply tensor_comp_mor.
        }
        rewrite !z_iso_after_z_iso_inv.
        rewrite tensor_id_id.
        apply id_left.
      - intros x y f.
        cbn ; unfold from_enrichment_path_functor_inv_data.
        use z_iso_inv_on_left.
        refine (!_).
        exact (pr1 (pr222 F) x y f).
    Qed.

    Definition from_enrichment_path_functor_inv
      : functor_enrichment (functor_identity _) E₂ E₁
      := from_enrichment_path_functor_inv_data
         ,,
         from_enrichment_path_functor_inv_is_functor.

    Definition from_enrichment_path_unit
      : nat_trans_enrichment
          (nat_trans_id (functor_identity _))
          (functor_id_enrichment E₁)
          (functor_comp_enrichment
             from_enrichment_path_functor
             from_enrichment_path_functor_inv).
    Proof.
      intros x y.
      cbn.
      unfold from_enrichment_path_functor_data.
      unfold from_enrichment_path_functor_inv_data.
      rewrite !z_iso_inv_after_z_iso.
      rewrite !enriched_from_arr_id.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      etrans.
      {
        apply mon_rinvunitor_runitor.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    Qed.

    Definition from_enrichment_path_unit_inv
      : nat_trans_enrichment
          (nat_trans_id (functor_identity _))
          (functor_comp_enrichment
             from_enrichment_path_functor
             from_enrichment_path_functor_inv)
          (functor_id_enrichment E₁).
    Proof.
      intros x y.
      cbn.
      unfold from_enrichment_path_functor_data.
      unfold from_enrichment_path_functor_inv_data.
      rewrite !z_iso_inv_after_z_iso.
      rewrite !enriched_from_arr_id.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      etrans.
      {
        apply mon_rinvunitor_runitor.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    Qed.

    Definition from_enrichment_path_counit
      : nat_trans_enrichment
          (nat_trans_id _)
          (functor_comp_enrichment
             from_enrichment_path_functor_inv
             from_enrichment_path_functor)
          (functor_id_enrichment E₂).
    Proof.
      intros x y.
      cbn.
      unfold from_enrichment_path_functor_data.
      unfold from_enrichment_path_functor_inv_data.
      rewrite !enriched_from_arr_id.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      etrans.
      {
        apply mon_rinvunitor_runitor.
      }
      refine (!_).
      rewrite z_iso_after_z_iso_inv.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    Qed.

    Definition from_enrichment_path_counit_inv
      : nat_trans_enrichment
          (nat_trans_id _)
          (functor_id_enrichment E₂)
          (functor_comp_enrichment
             from_enrichment_path_functor_inv
             from_enrichment_path_functor).
    Proof.
      intros x y.
      cbn.
      unfold from_enrichment_path_functor_data.
      unfold from_enrichment_path_functor_inv_data.
      rewrite !enriched_from_arr_id.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      etrans.
      {
        apply mon_linvunitor_lunitor.
      }
      refine (!_).
      rewrite z_iso_after_z_iso_inv.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      apply mon_rinvunitor_runitor.
    Qed.

    Definition from_enrichment_path
      : ∑ (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
          (F₂ : functor_enrichment (functor_identity _) E₂ E₁),
        nat_trans_enrichment
          (nat_trans_id (functor_identity _))
          (functor_id_enrichment E₁)
          (functor_comp_enrichment F₁ F₂)
        ×
        nat_trans_enrichment
          (nat_trans_id _)
          (functor_comp_enrichment F₂ F₁)
          (functor_id_enrichment E₂)
        ×
        nat_trans_enrichment
          (nat_trans_id _)
          (functor_comp_enrichment F₁ F₂)
          (functor_id_enrichment E₁)
        ×
        nat_trans_enrichment
          (nat_trans_id _)
          (functor_id_enrichment E₂)
          (functor_comp_enrichment F₂ F₁)
      := from_enrichment_path_functor
         ,,
         from_enrichment_path_functor_inv
         ,,
         from_enrichment_path_unit
         ,,
         from_enrichment_path_counit
         ,,
         from_enrichment_path_unit_inv
         ,,
         from_enrichment_path_counit_inv.
  End FromEnrichmentPath.

  Section ToEnrichmentPath.
    Context {C : bicat_of_univ_cats}
            {E₁ E₂ : disp_bicat_of_enriched_cats C}
            (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
            (F₂ : functor_enrichment (functor_identity _) E₂ E₁)
            (η : nat_trans_enrichment
                   (nat_trans_id (functor_identity _))
                   (functor_id_enrichment E₁)
                   (functor_comp_enrichment F₁ F₂))
            (ε : nat_trans_enrichment
                   (nat_trans_id _)
                   (functor_comp_enrichment F₂ F₁)
                   (functor_id_enrichment E₂)).

    Definition to_enrichment_path_inv_left
               (x y : (C : univalent_category))
      : pr1 F₁ x y · pr1 F₂ x y = identity _.
    Proof.
      pose (p := η x y).
      cbn in p.
      rewrite !enriched_from_arr_id in p.
      rewrite !assoc' in p.
      assert (mon_rinvunitor _
              · ((F₁ x y · F₂ x y) #⊗ enriched_id _ x
              · enriched_comp _ x x y)
              =
              identity _)
        as p'.
      {
        refine (p @ _).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply enrichment_id_left.
        }
        apply mon_linvunitor_lunitor.
      }
      refine (_ @ p').
      rewrite tensor_comp_r_id_l.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_rinvunitor.
      }
      rewrite !assoc' ; cbn.
      apply maponpaths.
      rewrite tensor_split'.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_rinvunitor.
      }
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      apply mon_rinvunitor_runitor.
    Qed.

    Definition to_enrichment_path_inv_right
               (x y : (C : univalent_category))
      : pr1 F₂ x y · pr1 F₁ x y = identity _.
    Proof.
      pose (p := ε x y).
      cbn in p.
      rewrite !enriched_from_arr_id in p.
      rewrite !assoc' in p.
      assert (mon_linvunitor _
              · (enriched_id _ y #⊗ (F₂ x y · F₁ x y)
              · enriched_comp _ x y y)
              =
              identity _)
        as p'.
      {
        refine (!p @ _).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply enrichment_id_right.
        }
        apply mon_rinvunitor_runitor.
      }
      refine (_ @ p').
      rewrite tensor_comp_l_id_l.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      rewrite !assoc' ; cbn.
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    Qed.

    Definition to_enrichment_path
      : enrichment_data_hom_path_help (pr1 E₁) (pr1 E₂).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - refine (λ x y, _).
        use make_z_iso.
        + exact (pr1 F₁ x y).
        + exact (pr1 F₂ x y).
        + split.
          * exact (to_enrichment_path_inv_left x y).
          * exact (to_enrichment_path_inv_right x y).
      - abstract
          (intros x ; cbn ;
           exact (pr12 F₁ x)).
      - abstract
          (intros x y z ; cbn ;
           exact (pr122 F₁ x y z)).
      - abstract
          (intros x y f ; cbn ;
           exact (!(pr222 F₁ x y f))).
      - abstract
          (intros x y f ; cbn ;
           use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E₂ x y))) ;
           cbn ;
           rewrite !(enriched_from_to_arr E₂) ;
           refine (pr222 F₁ x y (enriched_to_arr (pr1 E₁) f) @ _) ;
           apply maponpaths_2 ;
           rewrite !(enriched_from_to_arr E₁) ;
           apply idpath).
    Defined.
  End ToEnrichmentPath.

  Definition disp_univalent_2_0_enriched_cats_help_path
             {C : bicat_of_univ_cats}
             {E₁ E₂ : disp_bicat_of_enriched_cats C}
             (F G : ∑ (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
                      (F₂ : functor_enrichment (functor_identity _) E₂ E₁),
                    nat_trans_enrichment
                      (nat_trans_id (functor_identity _))
                      (functor_id_enrichment E₁)
                      (functor_comp_enrichment F₁ F₂)
                    ×
                    nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_comp_enrichment F₂ F₁)
                      (functor_id_enrichment E₂)
                    ×
                    nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_comp_enrichment F₁ F₂)
                      (functor_id_enrichment E₁)
                    ×
                    nat_trans_enrichment
                      (nat_trans_id _)
                      (functor_id_enrichment E₂)
                      (functor_comp_enrichment F₂ F₁))
             (p : pr11 F = pr11 G)
             (q : pr112 F = pr112 G)
    : F = G.
  Proof.
    induction F as [ F₁ F₂ ].
    induction F₁ as [ F₁ HF₁ ].
    induction F₂ as [ F₂ R ].
    induction F₂ as [ F₂ HF₂ ].
    induction G as [ G₁ G₂ ].
    induction G₁ as [ G₁ HG₁ ].
    induction G₂ as [ G₂ Q ].
    induction G₂ as [ G₂ HG₂ ].
    cbn in *.
    induction p.
    induction q.
    assert (p : HF₁ = HG₁).
    {
      apply isaprop_is_functor_enrichment.
    }
    induction p.
    apply maponpaths.
    assert (p : HF₂ = HG₂).
    {
      apply isaprop_is_functor_enrichment.
    }
    induction p.
    apply maponpaths.
    repeat (apply isapropdirprod) ; apply isaprop_nat_trans_enrichment.
  Qed.

  Definition disp_univalent_2_0_enriched_cats_help
             {C : bicat_of_univ_cats}
             (E₁ E₂ : disp_bicat_of_enriched_cats C)
    : enrichment_data_hom_path_help (pr1 E₁) (pr1 E₂)
      ≃
      (∑ (F₁ : functor_enrichment (functor_identity _) E₁ E₂)
         (F₂ : functor_enrichment (functor_identity _) E₂ E₁),
       nat_trans_enrichment
         (nat_trans_id (functor_identity _))
         (functor_id_enrichment E₁)
         (functor_comp_enrichment F₁ F₂)
       ×
       nat_trans_enrichment
         (nat_trans_id _)
         (functor_comp_enrichment F₂ F₁)
         (functor_id_enrichment E₂)
       ×
       nat_trans_enrichment
         (nat_trans_id _)
         (functor_comp_enrichment F₁ F₂)
         (functor_id_enrichment E₁)
       ×
       nat_trans_enrichment
         (nat_trans_id _)
         (functor_id_enrichment E₂)
         (functor_comp_enrichment F₂ F₁)).
  Proof.
    use weq_iso.
    - exact from_enrichment_path.
    - exact (λ F, to_enrichment_path (pr1 F) (pr12 F) (pr122 F) (pr1 (pr222 F))).
    - abstract
        (intros F ;
         use subtypePath ;
         [ intro ;
           repeat (apply isapropdirprod) ;
           repeat (use impred ; intro) ;
           apply homset_property
         | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         use z_iso_eq ;
         apply idpath).
    - abstract
        (intros F ;
         use disp_univalent_2_0_enriched_cats_help_path ;
         apply idpath).
  Defined.

  Definition disp_univalent_2_0_enriched_cats
             (HV : is_univalent V)
    : disp_univalent_2_0 disp_bicat_of_enriched_cats.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros C₁ E₁ E₂.
    use weqhomot.
    - exact (weq_disp_adjequiv_enriched _ _
             ∘ disp_univalent_2_0_enriched_cats_help E₁ E₂
             ∘ enrichment_data_hom_path HV _ _
             ∘ total2_paths_equiv _ _ _
             ∘ path_sigma_hprop _ _ _ (isaprop_enrichment_laws _))%weq.
    - abstract
        (intro p ;
         cbn in p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           apply isaprop_disp_left_adjoint_equivalence ;
           [ apply univalent_cat_is_univalent_2_1 | ] ;
           exact disp_univalent_2_1_enriched_cats
         | ] ;
         use subtypePath ;
         [ intro ; apply isaprop_is_functor_enrichment | ] ;
         apply idpath).
  Defined.

  Definition bicat_of_enriched_cats
    : bicat
    := total_bicat disp_bicat_of_enriched_cats.

  Definition is_univalent_2_1_bicat_of_enriched_cats
    : is_univalent_2_1 bicat_of_enriched_cats.
  Proof.
    use total_is_univalent_2_1.
    - exact univalent_cat_is_univalent_2_1.
    - exact disp_univalent_2_1_enriched_cats.
  Defined.

  Definition is_univalent_2_0_bicat_of_enriched_cats
             (HV : is_univalent V)
    : is_univalent_2_0 bicat_of_enriched_cats.
  Proof.
    use total_is_univalent_2_0.
    - exact univalent_cat_is_univalent_2_0.
    - use disp_univalent_2_0_enriched_cats.
      exact HV.
  Defined.

  Definition is_univalent_2_bicat_of_enriched_cats
             (HV : is_univalent V)
    : is_univalent_2 bicat_of_enriched_cats.
  Proof.
    split.
    - exact (is_univalent_2_0_bicat_of_enriched_cats HV).
    - exact is_univalent_2_1_bicat_of_enriched_cats.
  Defined.

  Definition underlying_cat
    : psfunctor bicat_of_enriched_cats bicat_of_univ_cats
    := pr1_psfunctor _.

  (** * 4. Accessors for the bicategory of enriched categories *)
  Definition enriched_cat
    : UU
    := bicat_of_enriched_cats.

  Coercion enriched_cat_to_univalent_category
           (E : enriched_cat)
    : univalent_category
    := pr1 E.

  Coercion enriched_cat_to_enrichment
           (E : enriched_cat)
    : enrichment E V
    := pr2 E.

  Definition make_enriched_cat
             (C : univalent_category)
             (E : enrichment C V)
    : enriched_cat
    := C ,, E.

  Definition enriched_functor
             (E₁ E₂ : enriched_cat)
    : UU
    := E₁ --> E₂.

  Coercion enriched_functor_to_functor
           {E₁ E₂ : enriched_cat}
           (F : enriched_functor E₁ E₂)
    : E₁ ⟶ E₂
    := pr1 F.

  Definition enriched_functor_enrichment
             {E₁ E₂ : enriched_cat}
             (F : enriched_functor E₁ E₂)
    : functor_enrichment F E₁ E₂
    := pr2 F.

  Definition make_enriched_functor
             {E₁ E₂ : enriched_cat}
             (F : E₁ ⟶ E₂)
             (EF : functor_enrichment F E₁ E₂)
    : enriched_functor E₁ E₂
    := F ,, EF.

  Definition enriched_nat_trans
             {E₁ E₂ : enriched_cat}
             (F G : enriched_functor E₁ E₂)
    : UU
    := F ==> G.

  Coercion enriched_nat_trans_to_nat_trans
           {E₁ E₂ : enriched_cat}
           {F G : enriched_functor E₁ E₂}
           (τ : enriched_nat_trans F G)
    : F ⟹ G
    := pr1 τ.

  Coercion enriched_nat_trans_enrichment
           {E₁ E₂ : enriched_cat}
           {F G : enriched_functor E₁ E₂}
           (τ : enriched_nat_trans F G)
    : nat_trans_enrichment τ (enriched_functor_enrichment F) (enriched_functor_enrichment G)
    := pr2 τ.

  Definition make_enriched_nat_trans
             {E₁ E₂ : enriched_cat}
             {F G : enriched_functor E₁ E₂}
             (τ : F ⟹ G)
             (Eτ : nat_trans_enrichment
                     τ
                     (enriched_functor_enrichment F)
                     (enriched_functor_enrichment G))
    : enriched_nat_trans F G
    := τ ,, Eτ.

  Definition eq_enriched_nat_trans
             {E₁ E₂ : enriched_cat}
             {F G : enriched_functor E₁ E₂}
             {τ₁ τ₂ : enriched_nat_trans F G}
             (p : ∏ (x : E₁), τ₁ x = τ₂ x)
    : τ₁ = τ₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_nat_trans_enrichment.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    exact p.
  Qed.

  Proposition from_eq_enriched_nat_trans
              {E₁ E₂ : enriched_cat}
              {F G : enriched_functor E₁ E₂}
              {τ₁ τ₂ : enriched_nat_trans F G}
              (p : τ₁ = τ₂)
              (x : E₁)
    : τ₁ x = τ₂ x.
  Proof.
    exact (maponpaths (λ z, pr11 z x) p).
  Qed.

  Definition from_is_invertible_2cell_enriched
             {E₁ E₂ : enriched_cat}
             {F G : enriched_functor E₁ E₂}
             (τ : invertible_2cell F G)
    : nat_z_iso F G.
  Proof.
    use invertible_2cell_to_nat_z_iso.
    exact (_ ,, psfunctor_is_iso underlying_cat τ).
  Defined.

  Definition make_is_invertible_2cell_enriched
             {E₁ E₂ : enriched_cat}
             {F G : enriched_functor E₁ E₂}
             (τ : enriched_nat_trans F G)
             (Hτ : is_nat_z_iso τ)
    : is_invertible_2cell τ.
  Proof.
    use make_is_invertible_2cell.
    - simple refine (_ ,, _).
      + exact (pr1 (nat_z_iso_inv (make_nat_z_iso _ _ _ Hτ))).
      + abstract
          (use nat_z_iso_inv_enrichment ;
           exact (pr2 τ)).
    - abstract
        (use eq_enriched_nat_trans ;
         intro x ;
         apply (z_iso_inv_after_z_iso (_ ,, Hτ x))).
    - abstract
        (use eq_enriched_nat_trans ;
         intro x ;
         apply (z_iso_after_z_iso_inv (_ ,, Hτ x))).
  Defined.
End EnrichedCats.

Arguments make_enriched_cat {V} C E.
Arguments enriched_functor {V} E₁ E₂.
Arguments enriched_functor_enrichment {V E₁ E₂} F.
Arguments make_enriched_functor {V E₁ E₂} F EF.
Arguments enriched_nat_trans {V E₁ E₂} F G.
Arguments make_enriched_nat_trans {V E₁ E₂ F G} τ Eτ.
Arguments from_eq_enriched_nat_trans {V E₁ E₂ F G τ₁ τ₂} p x.
