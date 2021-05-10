Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Definition vcomp_rinvunitor
           {C : bicat}
           {a b : C}
           {f g : a --> b}
           (α : f ==> g)
  : rinvunitor f • (α ▹ _) = α • rinvunitor g.
Proof.
  use vcomp_move_R_pM.
  {
    is_iso.
  }
  simpl.
  rewrite !vassocr.
  use vcomp_move_L_Mp.
  {
    is_iso.
  }
  cbn.
  apply vcomp_runitor.
Qed.

Section DisplayedInserter.
  Context {B C : bicat}
          (F G : psfunctor B C).

  (*
    https://ncatlab.org/nlab/show/dialgebra
   *)
  Definition disp_inserter_disp_cat
    : disp_cat_ob_mor B.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ b, C⟦ F b , G b ⟧).
    - simpl.
      intros x y fx fy f.
      exact (#F f · fy ==> fx · #G f).
  Defined.

  Definition disp_inserter_disp_cat_id_comp
    : disp_cat_id_comp _ disp_inserter_disp_cat.
  Proof.
    use tpair.
    - simpl.
      intros x fx.
      exact (((psfunctor_id F x)^-1 ▹ fx)
               • lunitor _
               • rinvunitor _
               • (_ ◃ psfunctor_id G x)).
    - simpl.
      intros x y z f g fx fy fz αf βg.
      exact (((psfunctor_comp _ _ _)^-1 ▹ _)
               • rassociator _ _ _
               • (_ ◃ βg)
               • lassociator _ _ _
               • (αf ▹ _)
               • rassociator _ _ _
               • (_ ◃ psfunctor_comp _ _ _)).
  Defined.

  Definition disp_inserter_disp_cat_2cell
    : disp_2cell_struct disp_inserter_disp_cat.
  Proof.
    intros x y f g α fx fy αf βg.
    simpl in *.
    exact (##F α ▹ fy • βg
           =
           αf • (_ ◃ ##G α)).
  Defined.

  (*
  F C = C^op
  G C = Set
  #G f = id
  ##G f = id2
   *)

  Definition disp_inserter_prebicat_1
    : disp_prebicat_1_id_comp_cells B.
  Proof.
    use tpair.
    - use tpair.
      + exact disp_inserter_disp_cat.
      + exact disp_inserter_disp_cat_id_comp.
    - exact disp_inserter_disp_cat_2cell.
  Defined.

  Definition disp_inserter_ops
    : disp_prebicat_ops disp_inserter_prebicat_1.
  Proof.
    repeat split.
    - simpl ; red.
      intros x y f fx fy αf.
      rewrite !psfunctor_id2.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      reflexivity.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros x y f fx fy αf.
      rewrite !vassocl.
      use vcomp_move_L_pM.
      {
        is_iso.
      }
      cbn -[psfunctor_comp psfunctor_id].
      rewrite <- !rwhisker_vcomp.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            do 6 apply maponpaths_2.
            apply rwhisker_rwhisker.
          }
          rewrite !vassocr.
          do 7 apply maponpaths_2.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        apply idpath.
      }
      rewrite !vassocl.
      refine (!_).
      use vcomp_move_L_pM.
      {
        is_iso.
      }
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !rwhisker_vcomp.
        rewrite <- psfunctor_lunitor.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !lwhisker_vcomp.
        apply maponpaths.
        rewrite vassocr.
        rewrite <- psfunctor_lunitor.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        rewrite lwhisker_vcomp.
        rewrite linvunitor_lunitor.
        apply lwhisker_id2.
      }
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros x y f fx gx αf.
      rewrite !vassocl.
      use vcomp_move_L_pM.
      {
        is_iso.
      }
      cbn -[psfunctor_comp psfunctor_id].
      rewrite <- !lwhisker_vcomp.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        do 8 apply maponpaths_2.
        apply rwhisker_lwhisker_rassociator.
      }
      rewrite !vassocl.
      refine (!_).
      use vcomp_move_L_pM.
      {
        is_iso.
      }
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        rewrite <- psfunctor_runitor.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite <- psfunctor_runitor.
        apply idpath.
      }
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- left_unit_assoc.
      rewrite lwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply lunitor_lwhisker.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros x y f fx fy αf.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 7 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        rewrite !lwhisker_vcomp.
        rewrite <- psfunctor_linvunitor.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              rewrite !vassocr.
              rewrite rwhisker_rwhisker.
              rewrite !vassocl.
              apply maponpaths.
              apply lunitor_triangle.
            }
            rewrite !vassocr.
            rewrite <- vcomp_whisker.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite vcomp_lunitor.
        do 2 apply maponpaths.
        rewrite <- lunitor_triangle.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite !rwhisker_vcomp.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      do 3 (use vcomp_move_R_Mp ; is_iso).
      cbn -[psfunctor_comp psfunctor_id].
      rewrite id2_left.
      apply psfunctor_linvunitor.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros x y f fx fy αf.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rinvunitor_triangle.
        rewrite vcomp_rinvunitor.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- left_unit_inv_assoc.
        rewrite !lwhisker_vcomp.
        rewrite <- psfunctor_rinvunitor.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      do 3 (use vcomp_move_R_Mp ; is_iso).
      cbn -[psfunctor_comp psfunctor_id].
      rewrite id2_left.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      apply psfunctor_rinvunitor.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros w x y z f g h fw fx fy fz αf βg γh.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite rwhisker_rwhisker.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        do 12 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !rwhisker_vcomp.
          rewrite psfunctor_rassociator.
          apply idpath.
        }
        rewrite !rwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_rinv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 8 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite psfunctor_rassociator.
        rewrite !vassocl.
        rewrite <- !lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        do 9 apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite rwhisker_lwhisker_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          rewrite rwhisker_vcomp, lwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite lwhisker_id2, id2_rwhisker.
          apply idpath.
        }
        apply id2_left.
      }
      rewrite !vassocr.
      etrans.
      {
        do 8 apply maponpaths_2.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 6 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_4.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      do 2 apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      reflexivity.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      intros w x y z f g h fw fx fy fz αf αg αh.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_L_pM ; is_iso).
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        etrans.
        {
          do 7 apply maponpaths_2.
          rewrite !vassocl.
          apply maponpaths.
          rewrite vassocr.
          rewrite !rwhisker_vcomp.
          rewrite psfunctor_lassociator.
          rewrite <- !rwhisker_vcomp.
          apply idpath.
        }
        rewrite !vassocl.
        apply idpath.
      }
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        apply idpath.
      }
      use vcomp_move_R_Mp ; is_iso.
      {
        refine (psfunctor_is_iso G (lassociator _ _ _ ,, _)).
        is_iso.
      }
      cbn -[psfunctor_comp psfunctor_id].
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 13 apply maponpaths.
        rewrite !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite psfunctor_rassociator.
        apply idpath.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 9 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite rwhisker_rwhisker.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite <- vcomp_whisker.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - simpl ; cbn -[psfunctor_comp psfunctor_id] ; red.
      unfold disp_inserter_disp_cat_2cell.
      intros x y f g h α β fx fy αf βg γh p q.
      rewrite !psfunctor_vcomp.
      rewrite <- rwhisker_vcomp.
      rewrite <- lwhisker_vcomp.
      rewrite vassocl.
      rewrite q.
      rewrite vassocr.
      rewrite p.
      rewrite vassocl.
      reflexivity.
    - simpl ; cbn -[psfunctor_comp psfunctor_id].
      unfold disp_inserter_disp_cat_2cell.
      intros x y z f g₁ g₂ α fx fy fz αf βg₁ βg₂ hα.
      rewrite !vassocl.
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        do 6 apply maponpaths_2.
        rewrite !rwhisker_vcomp.
        rewrite psfunctor_lwhisker.
        rewrite !vassocl.
        rewrite vcomp_rinv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite hα.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite psfunctor_lwhisker.
      apply idpath.
    - simpl ; cbn -[psfunctor_comp psfunctor_id].
      unfold disp_inserter_disp_cat_2cell.
      intros x y z f₁ f₂ g α fx fy fz αf₁ αf₂ βg hα.
      rewrite !vassocl.
      use vcomp_move_L_pM ; is_iso.
      cbn -[psfunctor_comp psfunctor_id].
      etrans.
      {
        rewrite !vassocr.
        do 6 apply maponpaths_2.
        rewrite !rwhisker_vcomp.
        rewrite psfunctor_rwhisker.
        rewrite !vassocl.
        rewrite vcomp_rinv.
        rewrite id2_right.
        apply idpath.
      }
      etrans.
      {
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
        apply idpath.
      }
      do 3 apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite lwhisker_vcomp.
        rewrite psfunctor_rwhisker.
        rewrite <- lwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      exact (!hα).
      Time Qed.

  Definition disp_inserter_ops_laws
    : disp_prebicat_laws (_ ,, disp_inserter_ops).
  Proof.
    repeat split ; intro ; intros ; apply C.
  Qed.

  Definition disp_inserter_prebicat : disp_prebicat B
    := (_ ,, disp_inserter_ops_laws).

  Definition disp_inserter_bicat : disp_bicat B.
  Proof.
    refine (disp_inserter_prebicat ,, _).
    abstract
      (intros X Y f g α hX hY hf hg hα hβ ;
       apply isasetaprop ;
       cbn in * ; unfold disp_inserter_disp_cat_2cell in * ;
       apply C).
  Defined.

End DisplayedInserter.
