Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Limits.Products.

Local Open Scope cat.

Section BiadjunctionPreservation.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L).

  (**
   1. Preservation of products
   *)
  Section PreserveProducts.
    Context (HB₁ : is_univalent_2_1 B₁)
            (HB₂ : is_univalent_2_1 B₂)
            {y₁ y₂ : B₂}
            (p : binprod_cone y₁ y₂)
            (Hp : has_binprod_ump p)
            (x : B₁).

    Definition right_biadj_preserves_binprod_1cell
      : bicat_of_univ_cats
          ⟦ univ_hom HB₁ x (psfunctor_binprod_cone R p)
            ,
            univalent_category_binproduct
              (univ_hom HB₁ x (R y₁))
              (univ_hom HB₁ x (R y₂)) ⟧
      := biadj_left_hom R x p
         ∙ postcomp_binprod_cone HB₂ p (L x)
         ∙ pair_functor (biadj_right_hom R x y₁) (biadj_right_hom R x y₂).

    Definition left_adj_equiv_right_biadj_preserves_binprod_1cell
      : left_adjoint_equivalence right_biadj_preserves_binprod_1cell.
    Proof.
      use comp_left_adjoint_equivalence.
      - use (@comp_left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom _ _ _)
               (univ_hom _ _ _)
               (univalent_category_binproduct
                  (univ_hom _ _ _)
                  (univ_hom _ _ _))).
        + apply equiv_cat_to_adj_equiv.
          exact (biadj_hom_equiv R x p).
        + apply (has_binprod_ump_binprod_cat_ump _ _ Hp).
      - use equiv_cat_to_adj_equiv.
        use pair_adj_equivalence_of_cats.
        + exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y₁)).
        + exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y₂)).
    Defined.

    Definition right_biadj_preserves_binprod_nat_trans_data
      : nat_trans_data
          (postcomp_binprod_cone HB₁ (psfunctor_binprod_cone R p) x)
          (pr1 right_biadj_preserves_binprod_1cell).
    Proof.
      intro f.
      simple refine (_ ,, _) ; cbn ; cbn in f.
      - refine ((_ ◃ (linvunitor _ • (_ ▹ _) • rassociator _ _ _))
                • lassociator _ _ _
                • lassociator _ _ _
                • (((psnaturality_of (biadj_unit R) f)^-1 ▹ _) ▹ _)
                • (rassociator _ _ _ ▹ _)
                • rassociator _ _ _
                • (_ ◃ (psfunctor_comp R _ _ ▹ _))
                • (_ ◃ psfunctor_comp R _ _)).
        exact ((invertible_modcomponent_of (biadj_triangle_r R) p)^-1
                • lunitor _
                • (_ ◃ (lunitor _ • runitor _))).
      - refine ((_ ◃ (linvunitor _ • (_ ▹ _) • rassociator _ _ _))
                • lassociator _ _ _
                • lassociator _ _ _
                • (((psnaturality_of (biadj_unit R) f)^-1 ▹ _) ▹ _)
                • (rassociator _ _ _ ▹ _)
                • rassociator _ _ _
                • (_ ◃ (psfunctor_comp R _ _ ▹ _))
                • (_ ◃ psfunctor_comp R _ _)).
        exact ((invertible_modcomponent_of (biadj_triangle_r R) p)^-1
                • lunitor _
                • (_ ◃ (lunitor _ • runitor _))).
    Defined.

    Opaque psfunctor_comp.

    Definition right_biadj_preserves_binprod_is_nat_trans
      : is_nat_trans _ _ right_biadj_preserves_binprod_nat_trans_data.
    Proof.
      intros f₁ f₂ α.
      use pathsdirprod.
      - simpl.
        refine (vassocr _ _ _ @ _ @ vassocr _ _ _).
        etrans.
        {
          rewrite !vassocr.
          rewrite vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        do 2 apply maponpaths.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply maponpaths.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite !rwhisker_vcomp.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply maponpaths.
            refine (!_).
            exact (psnaturality_inv_natural (biadj_unit R) _ _ _ _ α).
          }
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          cbn.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite <- rwhisker_vcomp.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- !rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !lwhisker_vcomp.
        apply maponpaths.
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          refine (!_).
          apply psfunctor_rwhisker.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        refine (!_).
        apply psfunctor_rwhisker.
      - simpl.
        refine (vassocr _ _ _ @ _ @ vassocr _ _ _).
        etrans.
        {
          rewrite !vassocr.
          rewrite vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        do 2 apply maponpaths.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply maponpaths.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite !rwhisker_vcomp.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply maponpaths.
            refine (!_).
            exact (psnaturality_inv_natural (biadj_unit R) _ _ _ _ α).
          }
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          cbn.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite <- rwhisker_vcomp.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- !rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !lwhisker_vcomp.
        apply maponpaths.
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          refine (!_).
          apply psfunctor_rwhisker.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        refine (!_).
        apply psfunctor_rwhisker.
    Qed.

    Transparent psfunctor_comp.

    Definition right_biadj_preserves_binprod_nat_trans
      : postcomp_binprod_cone HB₁ (psfunctor_binprod_cone R p) x
        ⟹
        pr1 right_biadj_preserves_binprod_1cell.
    Proof.
      use make_nat_trans.
      - exact right_biadj_preserves_binprod_nat_trans_data.
      - exact right_biadj_preserves_binprod_is_nat_trans.
    Defined.

    Definition right_biadj_preserves_binprod_is_nat_iso
      : is_nat_iso right_biadj_preserves_binprod_nat_trans.
    Proof.
      intro.
      use is_iso_binprod_iso.
      + use is_inv2cell_to_is_iso.
        is_iso ; apply property_from_invertible_2cell.
      + use is_inv2cell_to_is_iso.
        is_iso ; apply property_from_invertible_2cell.
    Defined.

    Definition right_biadj_preserves_binprod_nat_iso
      : nat_iso
          (postcomp_binprod_cone HB₁ (psfunctor_binprod_cone R p) x)
          right_biadj_preserves_binprod_1cell.
    Proof.
      use make_nat_iso.
      - exact right_biadj_preserves_binprod_nat_trans.
      - exact right_biadj_preserves_binprod_is_nat_iso.
    Defined.
  End PreserveProducts.

  Definition right_biadj_preserves_binprods
             (HB₁ : is_univalent_2_1 B₁)
             (HB₂ : is_univalent_2_1 B₂)
    : preserves_binprods R.
  Proof.
    intros y₁ y₂ p Hp.
    use (has_binprod_cat_ump_binprod_ump HB₁).
    intro x.
    use left_adjoint_equivalence_invertible.
    - exact (right_biadj_preserves_binprod_1cell HB₁ HB₂ p x).
    - apply left_adj_equiv_right_biadj_preserves_binprod_1cell.
      exact Hp.
    - apply right_biadj_preserves_binprod_nat_trans.
    - use is_nat_iso_to_is_invertible_2cell.
      apply right_biadj_preserves_binprod_is_nat_iso.
  Defined.
End BiadjunctionPreservation.
