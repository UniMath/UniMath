(**********************************************************************

 The category of enriched functors

 We define the category of enriched functors and prove that it gives
 rise to a univalent category. To do so, we use displayed categories.

 **********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedFunctorCategory.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          (E₁ : enrichment C₁ V)
          (E₂ : enrichment C₂ V).

  Definition functor_enrichment_disp_cat_ob_mor
    : disp_cat_ob_mor [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact (λ F, functor_enrichment F E₁ E₂).
    - exact (λ F₁ F₂ FE₁ FE₂ α, nat_trans_enrichment (pr1 α) FE₁ FE₂).
  Defined.

  Definition functor_enrichment_disp_cat_id_comp
    : disp_cat_id_comp [C₁, C₂] functor_enrichment_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ F FE, id_trans_enrichment FE).
    - exact (λ F₁ F₂ F₃ τ θ FE₁ FE₂ FE₃ τE θE, comp_trans_enrichment τE θE).
  Defined.

  Definition functor_enrichment_disp_cat_data
    : disp_cat_data [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact functor_enrichment_disp_cat_ob_mor.
    - exact functor_enrichment_disp_cat_id_comp.
  Defined.

  Definition functor_enrichment_disp_cat
    : disp_cat [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact functor_enrichment_disp_cat_data.
    - abstract
        (repeat split ;
         intro ; intros ;
         try (apply isaprop_nat_trans_enrichment) ;
         apply isasetaprop ;
         apply isaprop_nat_trans_enrichment).
  Defined.

  Definition is_univalent_disp_functor_enrichment_disp_cat
    : is_univalent_disp functor_enrichment_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros F FE₁ FE₂.
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
      + rewrite <- !(functor_enrichment_id FE₁).
        rewrite (tensor_comp_r_id_l _ _ (FE₁ x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp FE₁).
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
      + rewrite <- !(functor_enrichment_id FE₂).
        rewrite (tensor_comp_l_id_l (FE₂ x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp FE₂).
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
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_nat_trans_enrichment.
  Qed.

  Definition enriched_functor_category
    : category
    := total_category functor_enrichment_disp_cat.

  Definition is_univalent_enriched_functor_cat
             (HC₂ : is_univalent C₂)
    : is_univalent enriched_functor_category.
  Proof.
    use is_univalent_total_category.
    - use is_univalent_functor_category.
      exact HC₂.
    - exact is_univalent_disp_functor_enrichment_disp_cat.
  Defined.
End EnrichedFunctorCategory.

Definition enriched_univalent_category
           {V : monoidal_cat}
           (C₁ C₂ : univalent_category)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : univalent_category
  := enriched_functor_category E₁ E₂ ,, is_univalent_enriched_functor_cat _ _ (pr2 C₂).
