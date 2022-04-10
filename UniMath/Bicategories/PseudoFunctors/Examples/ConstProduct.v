Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Section ConstProdPsfunctor.
  Context (B : bicat_with_binprod)
          (x : B).

  Definition const_prod_psfunctor_data
    : psfunctor_data B B.
  Proof.
    use make_psfunctor_data.
    - exact (λ y, y ⊗ x).
    - exact (λ y₁ y₂ f,  f ⊗₁ id₁ x).
    - exact (λ y₁ y₂ f g α, α ⊗₂ id₂ _).
    - exact (λ y, (pair_1cell_id_id_invertible B _ _)^-1).
    - exact (λ y₁ y₂ y₃ f g,
             pair_1cell_comp_invertible
               B
               f g
               (id₁ x) (id₁ x)
             • (id₂ _ ⊗₂ lunitor _)).
  Defined.

  Definition const_prod_psfunctor_laws
    : psfunctor_laws const_prod_psfunctor_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      apply pair_2cell_id_id.
    - intro ; intros ; cbn.
      refine (_ @ pair_2cell_comp _ _ _ _ _).
      rewrite id2_left.
      apply idpath.
    - intro ; intros ; cbn.
      refine (binprod_lunitor _ _ _ @ _).
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- pair_2cell_comp.
      rewrite id2_left, id2_right.
      apply idpath.
    - intro ; intros ; cbn.
      refine (binprod_runitor _ _ _ @ _).
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- pair_2cell_comp.
      rewrite id2_left, id2_right.
      rewrite runitor_lunitor_identity.
      apply idpath.
    - intro ; intros ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use binprod_ump_2cell_unique_alt.
      + apply (pr2 B).
      + rewrite <- !rwhisker_vcomp.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        etrans.
        {
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply binprod_ump_2cell_pr1.
          }
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply pair_2cell_pr1.
          }
          rewrite !vassocl.
          rewrite lwhisker_id2.
          rewrite id2_left.
          apply maponpaths.
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply binprod_ump_2cell_pr1.
          }
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply pair_2cell_pr1.
          }
          rewrite lwhisker_id2, id2_right.
          apply maponpaths.
          apply pair_2cell_pr1.
        }
        etrans.
        {
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            rewrite id2_left.
            rewrite !vassocl.
            do 6 apply maponpaths.
            rewrite !vassocr.
            rewrite vcomp_linv.
            rewrite id2_left.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite !vassocl.
          unfold pair_1cell_pr1.
          rewrite vcomp_linv, id2_right.
          rewrite vcomp_linv, id2_right.
          do 4 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_linv.
          rewrite id2_left.
          apply idpath.
        }
        rewrite <- lwhisker_vcomp.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite lassociator_lassociator.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          rewrite !vassocr.
          apply maponpaths.
          apply pair_2cell_pr1.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lwhisker_id2, id2_right.
        rewrite !vassocl.
        etrans.
        {
          do 4 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        unfold pair_1cell_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv, id2_right.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply pair_2cell_pr1.
          }
          rewrite lwhisker_id2, id2_right.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite !vassocl.
          rewrite vcomp_linv.
          rewrite id2_right.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply binprod_ump_2cell_pr1.
          }
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite !vassocl.
          rewrite vcomp_linv.
          rewrite id2_right.
          apply idpath.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        rewrite !vassocl.
        etrans.
        {
          do 9 apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocr.
        apply maponpaths_2.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
        rewrite !vassocl.
        rewrite <- lassociator_lassociator.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        rewrite id2_right.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        rewrite !vassocl.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocr.
        rewrite <- !lwhisker_vcomp.
        apply maponpaths_2.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        rewrite !vassocl.
        etrans.
        {
          do 5 apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          apply idpath.
        }
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          apply id2_left.
        }
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocr.
        refine (_ @ id2_left _).
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          apply id2_left.
        }
        apply lassociator_rassociator.
      + rewrite <- !rwhisker_vcomp.
        etrans.
        {
          do 4 apply maponpaths.
          apply pair_2cell_pr2.
        }
        refine (!_).
        etrans.
        {
          do 4 apply maponpaths.
          apply pair_2cell_pr2.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite lwhisker_id2.
        rewrite id2_right.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply pair_2cell_pr2.
        }
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply pair_2cell_pr2.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        refine (!_).
        rewrite <- lwhisker_vcomp.
        etrans.
        {
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        rewrite <- lwhisker_vcomp.
        etrans.
        {
          rewrite !vassocr.
          rewrite lwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        rewrite <- lwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        refine (!_).
        etrans.
        {
          rewrite <- lwhisker_vcomp.
          rewrite !vassocr.
          rewrite rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        etrans.
        {
          rewrite <- lwhisker_vcomp.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        unfold pair_1cell_pr2.
        rewrite !vcomp_linv, id2_right.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_right.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite id2_rwhisker.
          apply id2_left.
        }
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply pair_2cell_pr2.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite !lwhisker_vcomp.
          rewrite !vassocr.
          rewrite vcomp_linv.
          rewrite id2_left.
          rewrite !vassocl.
          rewrite vcomp_linv.
          rewrite id2_right.
          apply idpath.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker.
          rewrite !vassocl.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lunitor_lwhisker.
        rewrite rwhisker_vcomp.
        apply maponpaths.
        rewrite lunitor_runitor_identity.
        rewrite runitor_triangle.
        apply idpath.
    - intro ; intros ; cbn.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite id2_left, id2_right.
      rewrite !vassocr.
      rewrite <- binprod_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- pair_2cell_comp.
      rewrite lwhisker_id2, id2_left, id2_right.
      apply idpath.
    - intro ; intros ; cbn.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite id2_left, id2_right.
      rewrite !vassocr.
      rewrite <- binprod_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- pair_2cell_comp.
      rewrite id2_rwhisker, id2_left, id2_right.
      apply idpath.
  Qed.

  Definition const_prod_psfunctor_invertible_cells
    : invertible_cells const_prod_psfunctor_data.
  Proof.
    split.
    - intro y.
      apply is_invertible_2cell_inv.
    - intros y₁ y₂ y₃ f g ; cbn.
      is_iso.
      + apply binprod_ump_2cell_invertible.
        * is_iso.
          ** apply property_from_invertible_2cell.
          ** apply property_from_invertible_2cell.
        * is_iso.
          ** apply property_from_invertible_2cell.
          ** apply property_from_invertible_2cell.
      + apply binprod_ump_2cell_invertible.
        * is_iso.
          apply property_from_invertible_2cell.
        * is_iso.
          apply property_from_invertible_2cell.
  Defined.

  Definition const_prod_psfunctor
    : psfunctor B B.
  Proof.
    use make_psfunctor.
    - exact const_prod_psfunctor_data.
    - exact const_prod_psfunctor_laws.
    - exact const_prod_psfunctor_invertible_cells.
  Defined.
End ConstProdPsfunctor.
