(******************************************************************************************

 Whiskered transformations between enriched bifunctors

 In this file, we give a version of enriched transformations between enriched bifunctors,
 and the laws are written in a whiskered style. In a whiskered bifunctor, we have two
 actions rather than a single functorial action. For whiskered transformations, we thus
 also have two naturality laws, namely one for each action.

 Content
 1. Whiskered transformations between bifunctors
 2. Equivalence with enriched natural transformations

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

(** * 1. Whiskered transformations between bifunctors *)
Definition whiskered_enriched_transformation_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_whiskered_bifunctor E₁ E₂ E₃)
  : UU
  := ∏ (x : C₁) (y : C₂), F x y --> G x y.

Definition whiskered_enriched_transformation_laws
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : whiskered_enriched_transformation_data F G)
  : UU
  := (∏ (x₁ x₂ : C₁)
        (y : C₂),
      enriched_whiskered_bifunctor_left F x₁ x₂ y
      · postcomp_arr E₃ (F x₁ y) (τ x₂ y)
      =
      enriched_whiskered_bifunctor_left G x₁ x₂ y
      · precomp_arr E₃ (G x₂ y) (τ x₁ y))
     ×
     (∏ (x : C₁)
        (y₁ y₂ : C₂),
      enriched_whiskered_bifunctor_right F x y₁ y₂
      · postcomp_arr E₃ (F x y₁) (τ x y₂)
      =
      enriched_whiskered_bifunctor_right G x y₁ y₂
      · precomp_arr E₃ (G x y₂) (τ x y₁)).

Proposition isaprop_whiskered_enriched_transformation_laws
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            (τ : whiskered_enriched_transformation_data F G)
  : isaprop (whiskered_enriched_transformation_laws τ).
Proof.
  use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition whiskered_enriched_transformation
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_whiskered_bifunctor E₁ E₂ E₃)
  : UU
  := ∑ (τ : whiskered_enriched_transformation_data F G),
     whiskered_enriched_transformation_laws τ.

Definition make_whiskered_enriched_transformation
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : whiskered_enriched_transformation_data F G)
           (Hτ : whiskered_enriched_transformation_laws τ)
  : whiskered_enriched_transformation F G
  := τ ,, Hτ.

Definition whiskered_enriched_transformation_ob
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : whiskered_enriched_transformation F G)
           (x : C₁)
           (y : C₂)
  : F x y --> G x y
  := pr1 τ x y.

Coercion whiskered_enriched_transformation_ob
  : whiskered_enriched_transformation >-> Funclass.

Proposition whiskered_enriched_transformation_natural_left
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            (τ : whiskered_enriched_transformation F G)
            (x₁ x₂ : C₁)
            (y : C₂)
  : enriched_whiskered_bifunctor_left F x₁ x₂ y
    · postcomp_arr E₃ (F x₁ y) (τ x₂ y)
    =
    enriched_whiskered_bifunctor_left G x₁ x₂ y
    · precomp_arr E₃ (G x₂ y) (τ x₁ y).
Proof.
  exact (pr12 τ x₁ x₂ y).
Defined.

Proposition whiskered_enriched_transformation_natural_right
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            (τ : whiskered_enriched_transformation F G)
            (x : C₁)
            (y₁ y₂ : C₂)
  : enriched_whiskered_bifunctor_right F x y₁ y₂
    · postcomp_arr E₃ (F x y₁) (τ x y₂)
    =
    enriched_whiskered_bifunctor_right G x y₁ y₂
    · precomp_arr E₃ (G x y₂) (τ x y₁).
Proof.
  exact (pr22 τ x y₁ y₂).
Defined.

Proposition eq_whiskered_enriched_transformation
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            {τ θ : whiskered_enriched_transformation F G}
            (p : ∏ (x : C₁) (y : C₂), τ x y = θ x y)
  : τ = θ.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_whiskered_enriched_transformation_laws.
  }
  use funextsec ; intro x.
  use funextsec ; intro y.
  exact (p x y).
Qed.

(** * 2. Equivalence with enriched natural transformations *)
Definition whiskered_enriched_transformation_to_curried_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : whiskered_enriched_transformation F G)
  : curried_enriched_transformation_data
      (enriched_whiskered_bifunctor_to_curried F)
      (enriched_whiskered_bifunctor_to_curried G)
  := λ x y, τ x y.

Arguments whiskered_enriched_transformation_to_curried_data {V C₁ C₂ C₃ E₁ E₂ E₃ F G} τ /.

Proposition whiskered_enriched_transformation_to_curried_law
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            (τ : whiskered_enriched_transformation F G)
  : curried_enriched_transformation_law
      (whiskered_enriched_transformation_to_curried_data τ).
Proof.
  intros x₁ x₂ y₁ y₂ ; cbn.
  rewrite !assoc'.
  etrans.
  {
    rewrite enriched_comp_postcomp_arr.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    rewrite whiskered_enriched_transformation_natural_left.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite enriched_comp_precomp_arr.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    rewrite <- whiskered_enriched_transformation_natural_right.
    apply idpath.
  }
  rewrite tensor_comp_r_id_r.
  rewrite tensor_comp_l_id_r.
  rewrite !assoc'.
  apply maponpaths.
  rewrite precomp_postcomp_arr_assoc.
  apply idpath.
Qed.

Definition whiskered_enriched_transformation_to_curried
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : whiskered_enriched_transformation F G)
  : curried_enriched_transformation
      (enriched_whiskered_bifunctor_to_curried F)
      (enriched_whiskered_bifunctor_to_curried G).
Proof.
  use make_curried_enriched_transformation.
  - exact (whiskered_enriched_transformation_to_curried_data τ).
  - exact (whiskered_enriched_transformation_to_curried_law τ).
Defined.

Definition curried_enriched_transformation_to_whiskered_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation
                  (enriched_whiskered_bifunctor_to_curried F)
                  (enriched_whiskered_bifunctor_to_curried G))
  : whiskered_enriched_transformation_data F G
  := λ x y, τ x y.

Arguments curried_enriched_transformation_to_whiskered_data {V C₁ C₂ C₃ E₁ E₂ E₃ F G} τ /.

Proposition curried_enriched_transformation_to_whiskered_laws
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
            (τ : curried_enriched_transformation
                   (enriched_whiskered_bifunctor_to_curried F)
                   (enriched_whiskered_bifunctor_to_curried G))
  : whiskered_enriched_transformation_laws
      (curried_enriched_transformation_to_whiskered_data τ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    pose (maponpaths
            (λ z, mon_rinvunitor _ · identity _ #⊗ enriched_id _ _ · z)
            (curried_enriched_transformation_natural τ x₁ x₂ y y)) as p.
    refine (_ @ p @ _) ; cbn ; clear p.
    + rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite !enriched_whiskered_bifunctor_right_id.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_rinvunitor_runitor.
      apply id_left.
    + rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite !enriched_whiskered_bifunctor_right_id.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_rinvunitor_runitor.
      apply id_left.
  - intros x y₁ y₂ ; cbn.
    pose (maponpaths
            (λ z, mon_linvunitor _ · enriched_id _ _ #⊗ identity _ · z)
            (curried_enriched_transformation_natural τ x x y₁ y₂)) as p.
    refine (_ @ p @ _) ; cbn ; clear p.
    + rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite !enriched_whiskered_bifunctor_left_id.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        rewrite tensor_lunitor.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      apply id_left.
    + rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite !enriched_whiskered_bifunctor_left_id.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        rewrite tensor_lunitor.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      apply id_left.
Qed.

Definition curried_enriched_transformation_to_whiskered
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_whiskered_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation
                  (enriched_whiskered_bifunctor_to_curried F)
                  (enriched_whiskered_bifunctor_to_curried G))
  : whiskered_enriched_transformation F G.
Proof.
  use make_whiskered_enriched_transformation.
  - exact (curried_enriched_transformation_to_whiskered_data τ).
  - exact (curried_enriched_transformation_to_whiskered_laws τ).
Defined.

Definition curried_enriched_transformation_whiskered_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_whiskered_bifunctor E₁ E₂ E₃)
  : curried_enriched_transformation
      (enriched_whiskered_bifunctor_to_curried F)
      (enriched_whiskered_bifunctor_to_curried G)
    ≃
    whiskered_enriched_transformation F G.
Proof.
  use weq_iso.
  - exact curried_enriched_transformation_to_whiskered.
  - exact whiskered_enriched_transformation_to_curried.
  - abstract
      (intro τ ;
       use eq_curried_enriched_transformation ;
       intros x y ;
       apply idpath).
  - abstract
      (intro τ ;
       use eq_whiskered_enriched_transformation ;
       intros x y ;
       apply idpath).
Defined.

Definition enriched_nat_trans_whiskered_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_whiskered_bifunctor E₁ E₂ E₃)
  : enriched_nat_trans
      (enriched_curried_bifunctor_to_bifunctor
         (enriched_whiskered_bifunctor_to_curried F))
      (enriched_curried_bifunctor_to_bifunctor
         (enriched_whiskered_bifunctor_to_curried G))
    ≃
    whiskered_enriched_transformation F G
  := (curried_enriched_transformation_whiskered_weq F G
      ∘ enriched_nat_trans_curried_weq _ _)%weq.
