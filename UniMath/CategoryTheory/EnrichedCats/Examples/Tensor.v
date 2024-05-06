(******************************************************************************************

 The tensor of enriched categories

 Suppose that we have two categories `E₁` and `E₂` enriched over some symmetric monoidal
 category `V`. There are multiple ways to take their product. If `V` has binary products,
 then we could take the following product:
 - Objects: pairs of objects in `E₁` and `E₂`
 - Morphisms from `(x₁ , y₁)` to `(x₂ , y₂)`: take the product of the objects of morphisms
   from `x₁` to `x₂` and from `y₁` to `y₂`

 However, often one is different in a different product operation. Rather than using binary
 products in `V` to construct hom-objects, we use the tensor in `V` to do so. More
 specifically, we define
 - Objects: pairs of objects in `E₁` and `E₂`
 - Morphisms from `(x₁ , y₁)` to `(x₂ , y₂)`: take the tensor of the objects of morphisms
   from `x₁` to `x₂` and from `y₁` to `y₂`

 We can see their difference by thinking of an example. For example, if we look at
 categories enriched over abelian groups, then the first construction would use of the
 binary product of abelian groups, whereas the second construction would use the tensor
 product of abelian groups. Another example would be pointed posets: for the first
 construction, we would use binary products, while for the second construction, we would
 use smash products.

 In applications, one often uses the second construction. For example, enriched profunctors
 and enriched monoidal categories are defined using the tensor product of enriched
 categories and not the binary product.

 Another interesting feature of this construction, is that in general, it does not preserve
 underlying categories and it does not necessarily interact nicely with univalence. The
 reason for that is as follows: the identity type of objects is given by pairs of identities
 between the two individual components. If we want the tensor to be univalent, then
 isomorphisms in the tensor should be given by pairs of isomorphisms. This would be
 guaranteed if `V` is cartesian, but not in general

 Contents
 1. The data of the tensor
 2. The axioms
 3. The tensor of enriched categories

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section Tensor.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ : category}
          (E₁ : enrichment C₁ V)
          (E₂ : enrichment C₂ V).

  (** * 1. The data of the tensor *)
  Definition tensor_enriched_precat_data
    : enriched_precat_data V.
  Proof.
    use make_enriched_precat_data.
    - exact (C₁ × C₂).
    - exact (λ x y, E₁ ⦃ pr1 x , pr1 y ⦄ ⊗ (E₂ ⦃ pr2 x , pr2 y ⦄)).
    - exact (λ x, mon_linvunitor _ · (enriched_id E₁ _ #⊗ enriched_id E₂ _)).
    - exact (λ x y z,
             inner_swap _ _ _ _ _
             · (enriched_comp E₁ _ _ _ #⊗ enriched_comp E₂ _ _ _)).
  Defined.

  (** * 2. The axioms *)
  Proposition tensor_enriched_precat_id_ax
    : enriched_id_ax tensor_enriched_precat_data.
  Proof.
    intros x y.
    induction x as [ x₁ x₂ ].
    induction y as [ y₁ y₂ ].
    split ; cbn.
    - rewrite !assoc.
      rewrite tensor_comp_r_id_r.
      rewrite <- tensor_id_id.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- naturality_inner_swap.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite <- !enrichment_id_left.
        apply idpath.
      }
      rewrite <- precompose_inner_swap_with_lunitors_on_right.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply inner_swap_inv.
      }
      rewrite id_left.
      rewrite tensor_mor_right.
      rewrite !assoc.
      rewrite tensor_id_id.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_id_r.
      }
      rewrite mon_linvunitor_lunitor.
      rewrite tensor_id_id.
      apply id_left.
    - rewrite !assoc.
      rewrite tensor_comp_l_id_r.
      rewrite <- tensor_id_id.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- naturality_inner_swap.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite <- !enrichment_id_right.
        apply idpath.
      }
      rewrite <- precompose_inner_swap_with_lunitors_and_runitor.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply inner_swap_inv.
      }
      rewrite id_left.
      rewrite tensor_mor_left.
      rewrite !assoc.
      rewrite tensor_id_id.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_id_l.
      }
      rewrite mon_linvunitor_lunitor.
      rewrite tensor_id_id.
      apply id_left.
  Qed.

  Proposition tensor_enriched_precat_assoc_ax
    : enriched_assoc_ax tensor_enriched_precat_data.
  Proof.
    intros w x y z.
    induction w as [ w₁ w₂ ].
    induction x as [ x₁ x₂ ].
    induction y as [ y₁ y₂ ].
    induction z as [ z₁ z₂ ].
    cbn.
    etrans.
    {
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_id_id.
      rewrite <- naturality_inner_swap.
      apply idpath.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite <- tensor_comp_mor.
      rewrite !enrichment_assoc.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc'.
      rewrite !tensor_comp_mor.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_l_id_r.
      rewrite !assoc'.
      rewrite <- tensor_id_id.
      rewrite <- naturality_inner_swap.
      apply idpath.
    }
    rewrite !assoc.
    do 2 apply maponpaths_2.
    rewrite tensor_id_id.
    rewrite !assoc'.
    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
    {
      use tensor_is_z_iso ; [ apply inner_swap_is_z_isomorphism | ].
      apply identity_is_z_iso.
    }
    cbn.
    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
    {
      apply inner_swap_is_z_isomorphism.
    }
    cbn.
    rewrite !assoc.
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      apply inner_swap_is_z_isomorphism.
    }
    cbn.
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      use tensor_is_z_iso ; [ | apply inner_swap_is_z_isomorphism ].
      apply identity_is_z_iso.
    }
    cbn.
    rewrite !assoc'.
    refine (_ @ inner_swap_hexagon _ _ _ _ _ _ _ @ _).
    - apply maponpaths.
      apply maponpaths_2.
      rewrite tensor_mor_right.
      apply idpath.
    - do 2 apply maponpaths.
      rewrite tensor_mor_left.
      apply idpath.
  Qed.

  (** * 3. The tensor of enriched categories *)
  Definition tensor_enriched_precat
    : enriched_precat V.
  Proof.
    use make_enriched_precat.
    - exact tensor_enriched_precat_data.
    - exact tensor_enriched_precat_id_ax.
    - exact tensor_enriched_precat_assoc_ax.
  Defined.

  Definition tensor_cat_with_enrichment
    : cat_with_enrichment V.
  Proof.
    use enriched_precat_weq_cat_with_enrichment.
    exact tensor_enriched_precat.
  Defined.

  Definition tensor_underlying_cat
    : category
    := tensor_cat_with_enrichment.

  Definition tensor_enrichment
    : enrichment tensor_underlying_cat V
    := tensor_cat_with_enrichment.
End Tensor.
