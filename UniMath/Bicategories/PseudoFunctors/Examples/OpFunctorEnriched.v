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

  Local Notation "∁" := (bicat_of_enriched_cats V). (* \C *)

  Definition op_enriched_psfunctor_data
    : psfunctor_data
        (op2_bicat (bicat_of_enriched_cats V))
        (bicat_of_enriched_cats V).
  Proof.
    use make_psfunctor_data.
    - exact (λ E,
             op_unicat (pr1 E)
             ,,
             op_enrichment V (pr2 E)).
    - exact (λ E₁ E₂ F,
             functor_opp (pr1 F)
             ,,
             functor_op_enrichment V (pr2 F)).
    - exact (λ E₁ E₂ F₁ F₂ τ,
             op_nt (pr1 τ)
             ,,
             nat_trans_op_enrichment V _ (pr2 τ)).
    - exact (λ E,
             functor_identity_op _
             ,,
             functor_identity_op_enrichment V (pr2 E)).
    - exact (λ E₁ E₂ E₃ F G,
             functor_comp_op _ _
             ,,
             functor_comp_op_enrichment V (pr2 F) (pr2 G)).
  Defined.

  Proposition op_enriched_psfunctor_laws
    : psfunctor_laws op_enriched_psfunctor_data.
  Proof.
    repeat split ; intro ; intros ; use eq_2cell_enriched ; intro ; cbn.
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
    - intro E.
      use make_is_invertible_2cell.
      + exact (nat_z_iso_to_trans_inv
                 (functor_identity_op_nat_z_iso _)
               ,,
               functor_identity_op_inv_enrichment V (pr2 E)).
      + abstract
          (use eq_2cell_enriched ;
           intro x ; cbn ;
           apply id_left).
      + abstract
          (use eq_2cell_enriched ;
           intro x ; cbn ;
           apply id_left).
    - intros E₁ E₂ E₃ F G.
      use make_is_invertible_2cell.
      + exact (nat_z_iso_to_trans_inv
                 (functor_comp_op_nat_z_iso _ _)
               ,,
               functor_comp_op_inv_enrichment V (pr2 F) (pr2 G)).
      + abstract
          (use eq_2cell_enriched ;
           intro x ; cbn ;
           apply id_left).
      + abstract
          (use eq_2cell_enriched ;
           intro x ; cbn ;
           apply id_left).
  Defined.

  Definition op_enriched_psfunctor
    : psfunctor (op2_bicat ∁) ∁.
  Proof.
    use make_psfunctor.
    - exact op_enriched_psfunctor_data.
    - exact op_enriched_psfunctor_laws.
    - exact op_enriched_psfunctor_inv2cells.
  Defined.
End OppositePseudofunctor.
