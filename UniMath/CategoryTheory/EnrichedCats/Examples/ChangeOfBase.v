(*****************************************************************

 Change of base for enriched categories

 In this file, we define the change of base for enriched
 categories. In textbooks, this construction works as follows: if
 we have two monoidal categories `V₁` and `V₂` and a lax monoidal
 functor `F : V₁ ⟶ V₂`, then every category enriched over `V₁`
 gives rise to a category enriched over `V₂`. The objects stay the
 same and for the enriched morphisms, we use the functor `F`.

 However, in a univalent setting, we would like to restrict this
 construction. Let `V₁` be any monoidal category (for example,
 `Set`) and let `V₂` be the terminal monoidal category (only one
 object and only one morphism). Then we have a functor `V₁ ⟶ V₂`
 and as such, every category enriched over `V₁` is also enriched
 over the terminal monoidal category. However, between any two
 objects in a category enriched over the terminal monoidal
 category, there is at most one isomorphism. As such, if we leave
 the objects the same in this construction, this does not in
 general give rise to a univalent category.

 To guarantee that the change of base actually gives rise to a
 univalent category, we make two assumptions:
 - The functor `F` is fully faithful
 - The functor `F` is a strong monoidal functor
 Using these assumptions, the underlying category of the change
 of base remains the same: the only thing that changes, is the
 enrichment. As such, univalence of the change of base follows
 directly from the univalence of the original category.

 We also discuss the action of the change of base on functors
 and natural transformations.

 Contents
 1. Change of base: enrichment for categories
 2. Change of base: enrichment for functors
 3. Change of base: enrichment for natural transformations

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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.

Local Open Scope cat.
Local Open Scope moncat.

Opaque fully_faithful_inv_hom.

Section ChangeOfBase.
  Context {V₁ V₂ : monoidal_cat}
          (F : strong_monoidal_functor V₁ V₂)
          (HF : fully_faithful F).

  (**
   1. Change of base: enrichment for categories
   *)
  Section Enrichment.
    Context {C : category}
            (E : enrichment C V₁).

    Definition change_of_base_enrichment_data
      : enrichment_data C V₂.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - exact (λ x y, F (E ⦃ x , y ⦄)).
      - exact (λ x, mon_functor_unit F · #F (enriched_id E x)).
      - exact (λ x y z, mon_functor_tensor F _ _ · #F (enriched_comp E x y z)).
      - exact (λ x y f, mon_functor_unit F · #F (enriched_from_arr E f)).
      - exact (λ x y f,
               enriched_to_arr
                 E
                 (fully_faithful_inv_hom
                    HF
                    _ _
                    (strong_functor_unit_inv F · f))).
    Defined.

    Definition change_of_base_enrichment_laws
      : enrichment_laws change_of_base_enrichment_data.
    Proof.
      repeat split.
      - intros x y ; cbn.
        refine (mon_functor_lunitor F (E ⦃ x, y ⦄) @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          exact (enrichment_id_left E x y).
        }
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_mon_functor_tensor.
        }
        apply maponpaths_2.
        apply maponpaths.
        apply functor_id.
      - intros x y ; cbn.
        refine (mon_functor_runitor F (E ⦃ x, y ⦄) @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          exact (enrichment_id_right E x y).
        }
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_mon_functor_tensor.
        }
        do 2 apply maponpaths_2.
        apply functor_id.
      - intros w x y z ; cbn.
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply tensor_comp_id_l.
          }
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply functor_id.
          }
          apply (tensor_mon_functor_tensor F).
        }
        etrans.
        {
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (!_).
          apply (mon_functor_lassociator F).
        }
        etrans.
        {
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite <- !functor_comp.
          apply maponpaths.
          rewrite !assoc.
          refine (!_).
          apply enrichment_assoc.
        }
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            apply tensor_comp_id_r.
          }
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              refine (!_).
              apply functor_id.
            }
            apply (tensor_mon_functor_tensor F).
          }
          rewrite !assoc'.
          rewrite <- functor_comp.
          apply idpath.
        }
        apply idpath.
      - intros x y f ; cbn.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (strong_functor_unit_inv_unit F).
          }
          apply id_left.
        }
        rewrite fully_faithful_inv_hom_is_inv.
        apply enriched_to_from_arr.
      - intros x y f ; cbn.
        rewrite enriched_from_to_arr.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        exact (strong_functor_unit_unit_inv F).
      - intros x ; cbn.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (strong_functor_unit_inv_unit F).
          }
          apply id_left.
        }
        rewrite fully_faithful_inv_hom_is_inv.
        apply enriched_to_arr_id.
      - intros x y z f g ; cbn.
        refine (enriched_to_arr_comp E f g @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply maponpaths_2.
            apply tensor_comp_mor.
          }
          rewrite !assoc'.
          etrans.
          {
            do 3 apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply (tensor_mon_functor_tensor F).
          }
          rewrite !assoc'.
          rewrite <- functor_comp.
          rewrite !assoc.
          etrans.
          {
            do 3 apply maponpaths_2.
            apply tensor_linvunitor.
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            do 2 apply maponpaths_2.
            refine (!(tensor_comp_l_id_l _ _ _) @ _).
            apply maponpaths.
            apply strong_functor_unit_inv_unit.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (mon_functor_linvunitor F).
          }
          rewrite <- functor_comp.
          rewrite !assoc.
          apply idpath.
        }
        apply fully_faithful_inv_hom_is_inv.
    Qed.

    Definition change_of_base_enrichment
      : enrichment C V₂.
    Proof.
      simple refine (_ ,, _).
      - exact change_of_base_enrichment_data.
      - exact change_of_base_enrichment_laws.
    Defined.
  End Enrichment.

  (**
   2. Change of base: enrichment for functors
   *)
  Section EnrichmentFunctor.
    Context {C₁ C₂ : category}
            {H : C₁ ⟶ C₂}
            {E₁ : enrichment C₁ V₁}
            {E₂ : enrichment C₂ V₁}
            (HE : functor_enrichment H E₁ E₂).

    Definition change_of_base_functor_enrichment_laws
      : @is_functor_enrichment
          _ _ _
          H
          (change_of_base_enrichment E₁)
          (change_of_base_enrichment E₂)
          (λ x y : C₁, # F (HE x y)).
    Proof.
      repeat split.
      - intros x ; cbn.
        rewrite !assoc'.
        rewrite <- functor_comp.
        do 2 apply maponpaths.
        apply functor_enrichment_id.
      - intros x y z ; cbn.
        rewrite !assoc.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply (tensor_mon_functor_tensor F).
        }
        rewrite !assoc'.
        rewrite <- !functor_comp.
        do 2 apply maponpaths.
        refine (!_).
        apply functor_enrichment_comp.
      - intros x y f ; cbn.
        rewrite !assoc'.
        rewrite <- (functor_comp F).
        do 2 apply maponpaths.
        apply functor_enrichment_from_arr.
    Qed.

    Definition change_of_base_functor_enrichment
      : functor_enrichment
          H
          (change_of_base_enrichment E₁)
          (change_of_base_enrichment E₂).
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y, #F (HE x y)).
      - exact change_of_base_functor_enrichment_laws.
    Defined.
  End EnrichmentFunctor.

  (**
   3. Change of base: enrichment for natural transformations
   *)
  Section EnrichmentTransformation.
    Context {C₁ C₂ : category}
            {H₁ H₂ : C₁ ⟶ C₂}
            {τ : H₁ ⟹ H₂}
            {E₁ : enrichment C₁ V₁}
            {E₂ : enrichment C₂ V₁}
            {HE₁ : functor_enrichment H₁ E₁ E₂}
            {HE₂ : functor_enrichment H₂ E₁ E₂}
            (Hτ : nat_trans_enrichment τ HE₁ HE₂).

    Definition change_of_base_nat_trans_enrichment
      : nat_trans_enrichment
          τ
          (change_of_base_functor_enrichment HE₁)
          (change_of_base_functor_enrichment HE₂).
    Proof.
      intros x y ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_l_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (tensor_mon_functor_tensor F).
        }
        rewrite !assoc'.
        rewrite <- functor_comp.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply (mon_functor_rinvunitor F).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_r_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (tensor_mon_functor_tensor F).
        }
        rewrite !assoc'.
        rewrite <- functor_comp.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply (mon_functor_linvunitor F).
      }
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite !assoc.
      refine (!_).
      apply Hτ.
    Qed.
  End EnrichmentTransformation.
End ChangeOfBase.
