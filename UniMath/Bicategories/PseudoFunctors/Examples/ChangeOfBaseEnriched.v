(*****************************************************************

 The change of base pseudofunctor

 If we have a fully faithful strong monoidal functor between two
 monoidal categories, then we get a pseudofunctor between the two
 bicategories of enriched categories over them.

 Note that for the definition, we use displayed machinery.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.ChangeOfBase.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Definition change_of_base_disp_psfunctor
           {V₁ V₂ : monoidal_cat}
           (F : strong_monoidal_functor V₁ V₂)
           (HF : preserve_underlying F)
  : disp_psfunctor
      (disp_bicat_of_enriched_cats V₁)
      (disp_bicat_of_enriched_cats V₂)
      (id_psfunctor _).
Proof.
  use make_disp_psfunctor.
  - apply disp_2cell_isapprop_enriched_cats.
  - apply disp_locally_groupoid_enriched_cats.
  - exact (λ C E,
           change_of_base_enrichment F HF E).
  - exact (λ C₁ C₂ G E₁ E₂ EG,
           change_of_base_functor_enrichment F HF EG).
  - exact (λ C₁ C₂ G₁ G₂ τ E₁ E₂ EG₁ EG₂ Eτ,
           change_of_base_nat_trans_enrichment F HF Eτ).
  - exact (λ C E,
           change_of_base_enrichment_identity F HF E).
  - exact (λ C₁ C₂ C₃ G₁ G₂ E₁ E₂ E₃ EG₁ EG₂,
           change_of_base_enrichment_comp F HF EG₁ EG₂).
Defined.
