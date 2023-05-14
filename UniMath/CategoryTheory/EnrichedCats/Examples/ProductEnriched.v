(*********************************************************************************

 Product of enriched categories

 We show that the product of enriched categories is again enriched over the same
 monoidal category. For this, we assume that the monoidal category is cartesian.

 Note that this is different from what is usual in enriched category theory.
 Suppose that we have two category `E₁` and `E₂` enriched over some monoidal
 category `V`. Their product is usually defined as follows:
 - Objects: pairs `x : E₁` and y : E₂`
 - Morphisms from `(x₁ ,, y₁)` to `(x₂ ,, y₂)` are given by
 ```
 E₁ ⦃ x₁ , x₂ ⦄ ⊗ E₂ ⦃ y₁ , y₂ ⦄
 ```
 To guarantee that the composition can be defined, we need to assume that `V` is
 symmetric.

 In our setting, we would like the construction to be compatible with univalence.
 As such, the isomorphisms are determined: by univalence, isomorphisms from
 `(x₁ ,, y₁)` to `(x₂ ,, y₂)` should be the same as pairs of isomorphisms from
 `x₁` to `x₂` and `y₁` to `y₂`. For that reason, we would like the morphisms in
 the product to be pairs of morphisms in `E₁` and in `E₂`.

 This is not the case in general for arbitrary monoidal categories. For example,
 if we look at the category of abelian groups with the tensor product, then
 morphisms in the product are not necessarily pairs of morphisms. For that reason,
 we assume that `V` is cartesian, which is sufficient to guarantee that the
 morphisms in the product are pairs of morphisms.

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section ProductEnrichment.
  Context (V : monoidal_cat)
          (HV : is_cartesian V)
          {C₁ C₂ : category}
          (E₁ : enrichment C₁ V)
          (E₂ : enrichment C₂ V).

  Definition product_enrichment_hom
             (x₁ y₁ : C₁)
             (x₂ y₂ : C₂)
    : V
    := (E₁ ⦃ x₁ , y₁ ⦄) ⊗ (E₂ ⦃ x₂ , y₂ ⦄).

  Definition product_enrichment_id
             (x₁ : C₁)
             (x₂ : C₂)
    : I_{V} --> product_enrichment_hom x₁ x₁ x₂ x₂.
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (enriched_id E₁ x₁).
    - exact (enriched_id E₂ x₂).
  Defined.

  Proposition product_enrichment_id_pr1
              (x₁ : C₁)
              (x₂ : C₂)
    : product_enrichment_id x₁ x₂ · semi_cart_tensor_pr1 HV _ _
      =
      enriched_id E₁ x₁.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Proposition product_enrichment_id_pr2
              (x₁ : C₁)
              (x₂ : C₂)
    : product_enrichment_id x₁ x₂ · semi_cart_tensor_pr2 HV _ _
      =
      enriched_id E₂ x₂.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Definition product_enrichment_pr1_comp
             (x₁ y₁ z₁ : C₁)
             (x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂ ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      -->
      (E₁ ⦃ y₁, z₁ ⦄) ⊗ (E₁ ⦃ x₁, y₁ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (semi_cart_tensor_pr1 HV _ _ · semi_cart_tensor_pr1 HV _ _).
    - exact (semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr1 HV _ _).
  Defined.

  Proposition product_enrichment_pr1_comp_pr1
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_pr1_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr1 HV _ _
      =
      semi_cart_tensor_pr1 HV _ _ · semi_cart_tensor_pr1 HV _ _.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Proposition product_enrichment_pr1_comp_pr2
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_pr1_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr2 HV _ _
      =
      semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr1 HV _ _.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Definition product_enrichment_pr2_comp
             (x₁ y₁ z₁ : C₁)
             (x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂ ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      -->
      (E₂ ⦃ y₂, z₂ ⦄) ⊗ (E₂ ⦃ x₂, y₂ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (semi_cart_tensor_pr1 HV _ _ · semi_cart_tensor_pr2 HV _ _).
    - exact (semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr2 HV _ _).
  Defined.

  Proposition product_enrichment_pr2_comp_pr1
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_pr2_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr1 HV _ _
      =
      semi_cart_tensor_pr1 HV _ _ · semi_cart_tensor_pr2 HV _ _.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Proposition product_enrichment_pr2_comp_pr2
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_pr2_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr2 HV _ _
      =
      semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr2 HV _ _.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Definition product_enrichment_comp
             (x₁ y₁ z₁ : C₁)
             (x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂ ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      -->
      product_enrichment_hom x₁ z₁ x₂ z₂.
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (product_enrichment_pr1_comp x₁ y₁ z₁ x₂ y₂ z₂ · enriched_comp E₁ x₁ y₁ z₁).
    - exact (product_enrichment_pr2_comp x₁ y₁ z₁ x₂ y₂ z₂ · enriched_comp E₂ x₂ y₂ z₂).
  Defined.

  Proposition product_enrichment_comp_pr1
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr1 HV _ _
      =
      product_enrichment_pr1_comp x₁ y₁ z₁ x₂ y₂ z₂ · enriched_comp E₁ x₁ y₁ z₁.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Proposition product_enrichment_comp_pr2
              (x₁ y₁ z₁ : C₁)
              (x₂ y₂ z₂ : C₂)
    : product_enrichment_comp x₁ y₁ z₁ x₂ y₂ z₂
      · semi_cart_tensor_pr2 HV _ _
      =
      product_enrichment_pr2_comp x₁ y₁ z₁ x₂ y₂ z₂ · enriched_comp E₂ x₂ y₂ z₂.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Definition product_enrichment_from_arr
             {x₁ y₁ : C₁}
             {x₂ y₂ : C₂}
             (f : x₁ --> y₁)
             (g : x₂ --> y₂)
    : I_{V} --> product_enrichment_hom x₁ y₁ x₂ y₂.
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (enriched_from_arr E₁ f).
    - exact (enriched_from_arr E₂ g).
  Defined.

  Proposition product_enrichment_from_arr_pr1
             {x₁ y₁ : C₁}
             {x₂ y₂ : C₂}
             (f : x₁ --> y₁)
             (g : x₂ --> y₂)
    : product_enrichment_from_arr f g
      · semi_cart_tensor_pr1 HV _ _
      =
      enriched_from_arr E₁ f.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Proposition product_enrichment_from_arr_pr2
             {x₁ y₁ : C₁}
             {x₂ y₂ : C₂}
             (f : x₁ --> y₁)
             (g : x₂ --> y₂)
    : product_enrichment_from_arr f g
      · semi_cart_tensor_pr2 HV _ _
      =
      enriched_from_arr E₂ g.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
  Qed.

  Definition product_enrichment_to_arr
             {x₁ y₁ : C₁}
             {x₂ y₂ : C₂}
             (fg : I_{V} --> product_enrichment_hom x₁ y₁ x₂ y₂)
    : (x₁ --> y₁) × (x₂ --> y₂)
    := enriched_to_arr E₁ (fg · semi_cart_tensor_pr1 HV _ _)
       ,,
       enriched_to_arr E₂ (fg · semi_cart_tensor_pr2 HV _ _).

  Definition triple_pr1_pr1
             (w₁ x₁ y₁ z₁ : C₁)
             (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂
      ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      ⊗ product_enrichment_hom w₁ x₁ w₂ x₂
      -->
      (E₁ ⦃ y₁ , z₁ ⦄) ⊗ (E₁ ⦃ x₁ , y₁ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr1 HV _ _).
    - exact (semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr2 HV _ _
             · semi_cart_tensor_pr1 HV _ _).
  Defined.

  Definition triple_pr1
             (w₁ x₁ y₁ z₁ : C₁)
             (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂
      ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      ⊗ product_enrichment_hom w₁ x₁ w₂ x₂
      -->
      (E₁ ⦃ y₁ , z₁ ⦄) ⊗ (E₁ ⦃ x₁ , y₁ ⦄) ⊗ (E₁ ⦃ w₁ , x₁ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - apply triple_pr1_pr1.
    - exact (semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr1 HV _ _).
  Defined.

  Proposition triple_pr1_eq
              (w₁ x₁ y₁ z₁ : C₁)
              (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_comp x₁ y₁ z₁ x₂ y₂ z₂ #⊗ identity _
      · product_enrichment_pr1_comp w₁ x₁ z₁ w₂ x₂ z₂
      =
      triple_pr1 _ _ _ _ _ _ _ _
      · enriched_comp E₁ x₁ y₁ z₁ #⊗ identity _.
  Proof.
    use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
    - rewrite !assoc'.
      rewrite product_enrichment_pr1_comp_pr1.
      rewrite !assoc.
      rewrite cartesian_tensor_pr1.
      rewrite !assoc'.
      rewrite product_enrichment_comp_pr1.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cartesian_tensor_pr1.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
      }
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
      + etrans.
        {
          apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        }
        rewrite !assoc'.
        rewrite product_enrichment_pr1_comp_pr1.
        apply idpath.
      + etrans.
        {
          apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        }
        rewrite !assoc'.
        rewrite product_enrichment_pr1_comp_pr2.
        apply idpath.
    - rewrite !assoc'.
      rewrite product_enrichment_pr1_comp_pr2.
      rewrite !assoc.
      rewrite cartesian_tensor_pr2.
      rewrite !assoc'.
      rewrite id_left.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cartesian_tensor_pr2.
      }
      rewrite id_right.
      etrans.
      {
        apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
      }
      apply idpath.
  Qed.

  Definition triple_pr2_pr1
             (w₁ x₁ y₁ z₁ : C₁)
             (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂
      ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      ⊗ product_enrichment_hom w₁ x₁ w₂ x₂
      -->
      (E₂ ⦃ y₂ , z₂ ⦄) ⊗ (E₂ ⦃ x₂ , y₂ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - exact (semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr2 HV _ _).
    - exact (semi_cart_tensor_pr1 HV _ _
             · semi_cart_tensor_pr2 HV _ _
             · semi_cart_tensor_pr2 HV _ _).
  Defined.

  Definition triple_pr2
             (w₁ x₁ y₁ z₁ : C₁)
             (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_hom y₁ z₁ y₂ z₂
      ⊗ product_enrichment_hom x₁ y₁ x₂ y₂
      ⊗ product_enrichment_hom w₁ x₁ w₂ x₂
      -->
      (E₂ ⦃ y₂ , z₂ ⦄) ⊗ (E₂ ⦃ x₂ , y₂ ⦄) ⊗ (E₂ ⦃ w₂ , x₂ ⦄).
  Proof.
    use (BinProductArrow _ (is_cartesian_BinProduct HV _ _)).
    - apply triple_pr2_pr1.
    - exact (semi_cart_tensor_pr2 HV _ _ · semi_cart_tensor_pr2 HV _ _).
  Defined.

  Proposition triple_pr2_eq
              (w₁ x₁ y₁ z₁ : C₁)
              (w₂ x₂ y₂ z₂ : C₂)
    : product_enrichment_comp x₁ y₁ z₁ x₂ y₂ z₂ #⊗ identity _
      · product_enrichment_pr2_comp w₁ x₁ z₁ w₂ x₂ z₂
      =
      triple_pr2 _ _ _ _ _ _ _ _
      · enriched_comp E₂ x₂ y₂ z₂ #⊗ identity _.
  Proof.
    use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
    - rewrite !assoc'.
      rewrite product_enrichment_pr2_comp_pr1.
      rewrite !assoc.
      rewrite cartesian_tensor_pr1.
      rewrite !assoc'.
      rewrite product_enrichment_comp_pr2.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cartesian_tensor_pr1.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
      }
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
      + etrans.
        {
          apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        }
        rewrite !assoc'.
        rewrite product_enrichment_pr2_comp_pr1.
        apply idpath.
      + etrans.
        {
          apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        }
        rewrite !assoc'.
        rewrite product_enrichment_pr2_comp_pr2.
        apply idpath.
    - rewrite !assoc'.
      rewrite product_enrichment_pr2_comp_pr2.
      rewrite !assoc.
      rewrite cartesian_tensor_pr2.
      rewrite !assoc'.
      rewrite id_left.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cartesian_tensor_pr2.
      }
      rewrite id_right.
      etrans.
      {
        apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
      }
      apply idpath.
  Qed.

  Definition product_enrichment_data
    : enrichment_data (category_binproduct C₁ C₂) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ xy₁ xy₂, product_enrichment_hom (pr1 xy₁) (pr1 xy₂) (pr2 xy₁) (pr2 xy₂)).
    - exact (λ xy, product_enrichment_id (pr1 xy) (pr2 xy)).
    - exact (λ xy₁ xy₂ xy₃, product_enrichment_comp _ _ _ _ _ _).
    - exact (λ xy₁ xy₂ fg, product_enrichment_from_arr (pr1 fg) (pr2 fg)).
    - exact (λ xy₁ xy₂ fg, product_enrichment_to_arr fg).
  Defined.

  Proposition product_enrichment_laws
    : enrichment_laws product_enrichment_data.
  Proof.
    repeat split.
    - intros xy₁ xy₂.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)).
      + cbn.
        refine (mon_lunitor_pr1 _ _ _ @ _).
        rewrite enrichment_id_left.
        rewrite !assoc'.
        rewrite product_enrichment_comp_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr1.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply product_enrichment_id_pr1.
          }
          rewrite !assoc.
          apply maponpaths_2.
          rewrite cartesian_tensor_pr1.
          rewrite id_right.
          apply idpath.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr2.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite id_right.
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr2.
          }
          rewrite id_right.
          rewrite cartesian_tensor_pr2.
          apply idpath.
      + cbn.
        refine (mon_lunitor_pr2 _ _ _ @ _).
        rewrite enrichment_id_left.
        rewrite !assoc'.
        rewrite product_enrichment_comp_pr2.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr1.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply product_enrichment_id_pr2.
          }
          rewrite !assoc.
          apply maponpaths_2.
          rewrite cartesian_tensor_pr1.
          rewrite id_right.
          apply idpath.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr2.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite id_right.
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr2.
          }
          rewrite id_right.
          rewrite cartesian_tensor_pr2.
          apply idpath.
    - intros xy₁ xy₂.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)).
      + cbn.
        refine (mon_runitor_pr1 _ _ _ @ _).
        rewrite enrichment_id_right.
        rewrite !assoc'.
        rewrite product_enrichment_comp_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr1.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite !assoc'.
          rewrite id_left, id_right.
          rewrite cartesian_tensor_pr1.
          apply idpath.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr2.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite !assoc.
          rewrite !cartesian_tensor_pr2.
          rewrite id_right.
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          apply product_enrichment_id_pr1.
      + cbn.
        refine (mon_runitor_pr2 _ _ _ @ _).
        rewrite enrichment_id_right.
        rewrite !assoc'.
        rewrite product_enrichment_comp_pr2.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr1.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          refine (!_).
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite !assoc'.
          rewrite id_left, id_right.
          rewrite cartesian_tensor_pr1.
          apply idpath.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr2.
          etrans.
          {
            apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite !assoc.
          rewrite !cartesian_tensor_pr2.
          rewrite id_right.
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          apply product_enrichment_id_pr2.
    - intros w x y z.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
      + rewrite !assoc'.
        rewrite !product_enrichment_comp_pr1.
        rewrite !assoc.
        rewrite triple_pr1_eq.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          rewrite id_right.
          rewrite mon_lassociator_pr1.
          rewrite product_enrichment_pr1_comp_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite id_right.
          rewrite !assoc.
          rewrite mon_lassociator_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
          }
          apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        * rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite product_enrichment_pr1_comp_pr2.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply cartesian_tensor_pr2.
          }
          rewrite !assoc'.
          rewrite product_enrichment_comp_pr1.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite mon_lassociator_pr2.
          use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
          ** rewrite !assoc'.
             rewrite product_enrichment_pr1_comp_pr1.
             rewrite !assoc.
             rewrite mon_lassociator_pr2.
             rewrite cartesian_tensor_pr1.
             refine (!_).
             rewrite !assoc'.
             etrans.
             {
               apply maponpaths.
               apply cartesian_tensor_pr1.
             }
             rewrite !assoc.
             etrans.
             {
               apply maponpaths_2.
               apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
             }
             apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
          ** rewrite !assoc'.
             rewrite product_enrichment_pr1_comp_pr2.
             rewrite !assoc.
             rewrite mon_lassociator_pr2.
             rewrite cartesian_tensor_pr2.
             refine (!_).
             rewrite !assoc'.
             etrans.
             {
               apply maponpaths.
               apply cartesian_tensor_pr2.
             }
             rewrite !assoc.
             etrans.
             {
               apply maponpaths_2.
               apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
             }
             rewrite !id_right.
             apply idpath.
      + rewrite !assoc'.
        rewrite !product_enrichment_comp_pr2.
        rewrite !assoc.
        rewrite triple_pr2_eq.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply cartesian_tensor_pr1.
          }
          rewrite id_right.
          rewrite mon_lassociator_pr1.
          rewrite product_enrichment_pr2_comp_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply cartesian_tensor_pr1.
          }
          rewrite id_right.
          rewrite !assoc.
          rewrite mon_lassociator_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
          }
          apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
        * rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply cartesian_tensor_pr2.
          }
          rewrite product_enrichment_pr2_comp_pr2.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply cartesian_tensor_pr2.
          }
          rewrite !assoc'.
          rewrite product_enrichment_comp_pr2.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite mon_lassociator_pr2.
          use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
          ** rewrite !assoc'.
             rewrite product_enrichment_pr2_comp_pr1.
             rewrite !assoc.
             rewrite mon_lassociator_pr2.
             rewrite cartesian_tensor_pr1.
             refine (!_).
             rewrite !assoc'.
             etrans.
             {
               apply maponpaths.
               apply cartesian_tensor_pr1.
             }
             rewrite !assoc.
             etrans.
             {
               apply maponpaths_2.
               apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
             }
             apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
          ** rewrite !assoc'.
             rewrite product_enrichment_pr2_comp_pr2.
             rewrite !assoc.
             rewrite mon_lassociator_pr2.
             rewrite cartesian_tensor_pr2.
             refine (!_).
             rewrite !assoc'.
             etrans.
             {
               apply maponpaths.
               apply cartesian_tensor_pr2.
             }
             rewrite !assoc.
             etrans.
             {
               apply maponpaths_2.
               apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct HV _ _)).
             }
             rewrite !id_right.
             apply idpath.
    - intros x y f ; cbn.
      use pathsdirprod.
      + rewrite product_enrichment_from_arr_pr1.
        rewrite enriched_to_from_arr.
        apply idpath.
      + rewrite product_enrichment_from_arr_pr2.
        rewrite enriched_to_from_arr.
        apply idpath.
    - intros x y f ; cbn.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
      + refine (product_enrichment_from_arr_pr1 _ _ @ _).
        apply enriched_from_to_arr.
      + refine (product_enrichment_from_arr_pr2 _ _ @ _).
        apply enriched_from_to_arr.
    - intros x ; cbn.
      use pathsdirprod.
      + rewrite product_enrichment_id_pr1.
        apply enriched_to_arr_id.
      + rewrite product_enrichment_id_pr2.
        apply enriched_to_arr_id.
    - intros x y z f g ; cbn.
      use pathsdirprod.
      + rewrite (enriched_to_arr_comp E₁).
        apply maponpaths.
        rewrite !assoc'.
        apply maponpaths.
        rewrite product_enrichment_comp_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr1.
          rewrite !assoc.
          rewrite !cartesian_tensor_pr1.
          rewrite !assoc'.
          refine (cartesian_tensor_pr1 _ _ _ @ _).
          apply maponpaths.
          refine (!_).
          apply product_enrichment_from_arr_pr1.
        * rewrite !assoc'.
          rewrite product_enrichment_pr1_comp_pr2.
          rewrite !assoc.
          rewrite !cartesian_tensor_pr2.
          rewrite !assoc'.
          refine (cartesian_tensor_pr2 _ _ _ @ _).
          apply maponpaths.
          refine (!_).
          apply product_enrichment_from_arr_pr1.
      + rewrite (enriched_to_arr_comp E₂).
        apply maponpaths.
        rewrite !assoc'.
        apply maponpaths.
        rewrite product_enrichment_comp_pr2.
        rewrite !assoc.
        apply maponpaths_2.
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct HV _ _)) ; cbn.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr1.
          rewrite !assoc.
          rewrite !cartesian_tensor_pr1.
          rewrite !assoc'.
          refine (cartesian_tensor_pr1 _ _ _ @ _).
          apply maponpaths.
          refine (!_).
          apply product_enrichment_from_arr_pr2.
        * rewrite !assoc'.
          rewrite product_enrichment_pr2_comp_pr2.
          rewrite !assoc.
          rewrite !cartesian_tensor_pr2.
          rewrite !assoc'.
          refine (cartesian_tensor_pr2 _ _ _ @ _).
          apply maponpaths.
          refine (!_).
          apply product_enrichment_from_arr_pr2.
  Qed.

  Definition product_enrichment
    : enrichment (category_binproduct C₁ C₂) V
    := product_enrichment_data ,, product_enrichment_laws.
End ProductEnrichment.
