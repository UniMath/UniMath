(*****************************************************************

 The opposite pseudofunctor for enriched categories

 If we have a symmetric monoidal category, then taking the
 opposite of enriched categories is pseudofunctorial.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Local Open Scope cat.

Section OppositePseudofunctor.
  Context (V : sym_monoidal_cat).

  Definition op_enriched_psfunctor_data
    : psfunctor_data
        (op2_bicat (bicat_of_enriched_cats V))
        (bicat_of_enriched_cats V).
  Proof.
    use make_psfunctor_data.
    - refine (λ (E : enriched_cat V), _).
      use make_enriched_cat.
      + exact (op_unicat E).
      + exact (op_enrichment V E).
    - refine (λ (E₁ E₂ : enriched_cat V) (F : enriched_functor _ _), _).
      use make_enriched_functor.
      + exact (functor_opp F).
      + exact (functor_op_enrichment V (enriched_functor_enrichment F)).
    - refine (λ (E₁ E₂ : enriched_cat V)
                (F₁ F₂ : enriched_functor _ _)
                (τ : enriched_nat_trans _ _), _).
      use make_enriched_nat_trans.
      + exact (op_nt τ).
      + exact (nat_trans_op_enrichment V _ τ).
    - refine (λ (E : enriched_cat V), _).
      use make_enriched_nat_trans.
      + exact (functor_identity_op _).
      + exact (functor_identity_op_enrichment V E).
    - refine (λ (E₁ E₂ E₃ : enriched_cat V) (F G : enriched_functor _ _), _).
      use make_enriched_nat_trans.
      + exact (functor_comp_op _ _).
      + exact (functor_comp_op_enrichment
                 V
                 (enriched_functor_enrichment F)
                 (enriched_functor_enrichment G)).
  Defined.

  Proposition op_enriched_psfunctor_laws
    : psfunctor_laws op_enriched_psfunctor_data.
  Proof.
    repeat split ; intro ; intros ; use eq_enriched_nat_trans ; intro ; cbn.
    - apply idpath.
    - apply idpath.
    - rewrite !id_left.
      rewrite functor_id.
      apply idpath.
    - rewrite !id_left.
      apply idpath.
    - rewrite !id_left, !id_right.
      rewrite functor_id.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition op_enriched_psfunctor_inv2cells
    : invertible_cells op_enriched_psfunctor_data.
  Proof.
    split.
    - refine (λ (E : enriched_cat V), _).
      use make_is_invertible_2cell_enriched.
      intro x.
      apply is_z_isomorphism_identity.
    - refine (λ (E₁ E₂ E₃ : enriched_cat V) (F G : enriched_functor _ _), _).
      use make_is_invertible_2cell_enriched.
      intro x.
      apply is_z_isomorphism_identity.
  Defined.

  Definition op_enriched_psfunctor
    : psfunctor (op2_bicat (bicat_of_enriched_cats V)) (bicat_of_enriched_cats V).
  Proof.
    use make_psfunctor.
    - exact op_enriched_psfunctor_data.
    - exact op_enriched_psfunctor_laws.
    - exact op_enriched_psfunctor_inv2cells.
  Defined.
End OppositePseudofunctor.
