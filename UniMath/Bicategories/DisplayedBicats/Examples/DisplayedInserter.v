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
  Qed.

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

  (** Some properties of the displayed inserter *)
  Definition disp_inserter_locally_propositional
    : disp_2cells_isaprop disp_inserter_bicat.
  Proof.
    intro ; intros.
    apply C.
  Qed.

  Definition disp_inserter_locally_sym
    : disp_locally_sym disp_inserter_bicat.
  Proof.
    intros x y f g α fx fy αf βg hα ; simpl in * ; red in *.
    use vcomp_move_L_Mp.
    {
      is_iso.
      refine (psfunctor_is_iso G ((_ ^-1) ,, _)).
      is_iso.
    }
    simpl.
    rewrite !vassocl.
    use vcomp_move_R_pM.
    {
      is_iso.
      refine (psfunctor_is_iso F ((_ ^-1) ,, _)).
      is_iso.
    }
    simpl.
    rewrite hα.
    reflexivity.
  Qed.

  Definition disp_inserter_locally_groupoidal
    : disp_locally_groupoid disp_inserter_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - exact disp_inserter_locally_sym.
    - exact disp_inserter_locally_propositional.
  Defined.

  (** Local univalence *)
  Definition disp_inserter_bicat_univalent_2_1
    : disp_univalent_2_1 disp_inserter_bicat.
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros x y f fx fy αf βg.
    apply isweqimplimpl.
    - cbn ; unfold idfun.
      intro p.
      pose (pr1 p) as h.
      cbn in h.
      unfold disp_inserter_disp_cat_2cell in h.
      rewrite !psfunctor_id2 in h.
      rewrite id2_rwhisker, lwhisker_id2 in h.
      rewrite id2_left, id2_right in h.
      exact (!h).
    - cbn -[isaprop] ; unfold idfun.
      apply C.
    - apply isaproptotal2.
      + exact isaprop_is_disp_invertible_2cell.
      + intros.
        apply disp_inserter_locally_propositional.
  Qed.

  (** Global univalence *)
  Section DispAdjEquivToInv2Cell.
    Context {x : B}
            {fx fy : disp_inserter_bicat x}
            (α : disp_adjoint_equivalence
                   (internal_adjoint_equivalence_identity x)
                   fx fy).

    Definition disp_adjequiv_to_inv2cell_cell
      : fx ==> fy
      := linvunitor _
         • (psfunctor_id F x ▹ fx)
         • pr112 α
         • (fy ◃ (psfunctor_id G _)^-1)
         • runitor _.

    Definition disp_adjequiv_to_inv2cell_inv
      : fy ==> fx
      := linvunitor _
         • (psfunctor_id F x ▹ fy)
         • pr1 α
         • (fx ◃ (psfunctor_id G _)^-1)
         • runitor _.

    Definition disp_adjequiv_to_inv2cell_cell_inv
      : disp_adjequiv_to_inv2cell_cell • disp_adjequiv_to_inv2cell_inv = id2 _.
    Proof.
      unfold disp_adjequiv_to_inv2cell_cell, disp_adjequiv_to_inv2cell_inv.
      rewrite !vassocl.
      use vcomp_move_R_pM ; is_iso.
      use vcomp_move_R_pM ; is_iso.
      {
        apply psfunctor_id.
      }
      cbn -[psfunctor_id psfunctor_comp].
      rewrite !vassocr.
      use vcomp_move_R_Mp ; is_iso.
      use vcomp_move_R_Mp ; is_iso.
      cbn -[psfunctor_id psfunctor_comp].
      rewrite !vassocl.
      rewrite id2_left.



      pose (pr1 (pr212 α)) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      unfold disp_inserter_disp_cat_2cell in p.
      rewrite !vassocr in p.
      rewrite psfunctor_linvunitor in p.
      rewrite !rwhisker_vcomp in p.
      rewrite !vassocl in p.
      rewrite vcomp_rinv in p.
      rewrite id2_right in p.
      rewrite psfunctor_linvunitor in p.
      rewrite <- lwhisker_vcomp in p.
      assert (p' := maponpaths (λ z, z • (fx ◃ (psfunctor_comp G _ _)^-1)) p).
      cbn -[psfunctor_id psfunctor_comp] in p' ; clear p.
      rewrite !vassocl in p'.
      rewrite !lwhisker_vcomp in p'.
      rewrite vcomp_rinv in p'.
      rewrite lwhisker_id2 in p'.
      rewrite !id2_right in p'.
      rewrite <- rwhisker_vcomp in p'.
      rewrite !vassocl in p'.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) in p'.
      rewrite rwhisker_rwhisker_alt in p'.
      rewrite !vassocr in p'.
      rewrite <- linvunitor_assoc in p'.
      rewrite !vassocl in p'.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) in p'.
      rewrite vcomp_whisker in p'.
      rewrite !vassocl in p'.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) in p'.
      rewrite <- rwhisker_rwhisker in p'.
      rewrite !vassocl in p'.

      use (vcomp_rcancel (fx ◃ (linvunitor (# G (id₁ x)) • (psfunctor_id G x ▹ # G (id₁ x))))).
      {
        is_iso.
        apply psfunctor_id.
      }
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      refine (_ @ p') ; clear p'.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_runitor.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_R_pM ; is_iso.
      cbn -[psfunctor_id psfunctor_comp].
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        rewrite <- lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite runitor_triangle.
        rewrite <- vcomp_runitor.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.

      rewrite psfunctor_runitor.
      rewrite !vassocl.
      refine (_  @ id2_right _).
      apply maponpaths.
      use vcomp_move_R_pM.
      {
        apply psfunctor_comp.
      }
      cbn -[psfunctor_id psfunctor_comp].
      rewrite id2_right.
      refine (_  @ id2_left _).
      use vcomp_move_L_Mp ; is_iso.
      cbn -[psfunctor_id psfunctor_comp].
      rewrite !vassocl.
      rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite <- psfunctor_linvunitor.
      rewrite <- psfunctor_vcomp.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_linvunitor.
      rewrite psfunctor_id2.
      apply idpath.
    Qed.

    Definition disp_adjequiv_to_inv2cell_inv_cell
      : disp_adjequiv_to_inv2cell_inv • disp_adjequiv_to_inv2cell_cell = id2 _.
    Proof.
      unfold disp_adjequiv_to_inv2cell_cell, disp_adjequiv_to_inv2cell_inv.

      pose (pr2 (pr212 α)) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      unfold disp_inserter_disp_cat_2cell in p.
      rewrite !vassocr in p.

    Admitted.

    Definition disp_adjequiv_to_inv2cell
      : invertible_2cell fx fy.
    Proof.
      use make_invertible_2cell.
      - exact disp_adjequiv_to_inv2cell_cell.
      - use make_is_invertible_2cell.
        + exact disp_adjequiv_to_inv2cell_inv.
        + exact disp_adjequiv_to_inv2cell_cell_inv.
        + exact disp_adjequiv_to_inv2cell_inv_cell.
    Defined.
  End DispAdjEquivToInv2Cell.


  Definition TODO {A : UU} : A.
  Admitted.

  Section Inv2CellToDispAdjEquiv.
    Context {x : B}
            {fx fy : disp_inserter_bicat x}
            (α : invertible_2cell fx fy).

    Definition inv2_cell_to_disp_adjequiv_left_adj
      : # F (id₁ x) · fy ==> fx · # G (id₁ x)
      := ((psfunctor_id F x)^-1 ▹ fy)
           • lunitor _
           • α^-1
           • rinvunitor _
           • (_ ◃ psfunctor_id G x).

    Definition inv2_cell_to_disp_adjequiv_right_adj
      : # F (id₁ x) · fx ==> fy · # G (id₁ x)
      := ((psfunctor_id F x)^-1 ▹ fx)
           • lunitor _
           • α
           • rinvunitor _
           • (_ ◃ psfunctor_id G x).

    Definition inv2_cell_to_disp_adjequiv
      : disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity x)
          fx fy.
    Proof.
      use tpair.
      - exact inv2_cell_to_disp_adjequiv_left_adj.
      - use tpair.
        + use tpair.
          * exact inv2_cell_to_disp_adjequiv_right_adj.
          * split.
            ** apply TODO.
            ** apply TODO.
        + abstract
            (refine ((_ ,, _) ,, (_ ,, _)) ;
             try apply C ;
             apply disp_inserter_locally_groupoidal).
    Defined.
  End Inv2CellToDispAdjEquiv.

  Definition inv2_cell_to_disp_adjequiv_weq_left
             {x : B}
             {fx fy : disp_inserter_bicat x}
             (α : invertible_2cell fx fy)
    : disp_adjequiv_to_inv2cell (inv2_cell_to_disp_adjequiv α) = α.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    cbn.
    unfold disp_adjequiv_to_inv2cell_cell ; cbn -[psfunctor_id].
    unfold inv2_cell_to_disp_adjequiv_right_adj.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite lwhisker_id2.
        apply id2_left.
      }
      apply rinvunitor_runitor.
    }
    apply id2_right.
  Qed.

  Definition inv2_cell_to_disp_adjequiv_weq_right
             (HB : is_univalent_2_1 B)
             {x : B}
             {fx fy : disp_inserter_bicat x}
             (α : disp_adjoint_equivalence
                    (internal_adjoint_equivalence_identity x)
                    fx fy)
    : inv2_cell_to_disp_adjequiv (disp_adjequiv_to_inv2cell α) = α.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence ; try exact HB.
      exact disp_inserter_bicat_univalent_2_1.
    }
    simpl.
    unfold disp_adjequiv_to_inv2cell, inv2_cell_to_disp_adjequiv_left_adj
    ; cbn -[psfunctor_id].
    unfold disp_adjequiv_to_inv2cell_inv.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_linvunitor.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite vcomp_linv.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite runitor_rinvunitor.
      apply id2_left.
    }
    rewrite lwhisker_vcomp.
    rewrite vcomp_linv.
    rewrite lwhisker_id2.
    apply id2_right.
  Qed.

  Definition inv2_cell_to_disp_adjequiv_weq
             {x : B}
             (fx fy : disp_inserter_bicat x)
    : invertible_2cell fx fy
      ≃
      disp_adjoint_equivalence
        (internal_adjoint_equivalence_identity x)
        fx fy.
  Proof.
    use make_weq.
    - exact inv2_cell_to_disp_adjequiv.
    - use gradth.
      + exact disp_adjequiv_to_inv2cell.
      + exact inv2_cell_to_disp_adjequiv_weq_left.
      + exact inv2_cell_to_disp_adjequiv_weq_right.
  Defined.

  Definition disp_inserter_bicat_univalent_2_0
             (HB : is_univalent_2_1 B)
             (HC : is_univalent_2_1 C)
    : disp_univalent_2_0 disp_inserter_bicat.
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x fx fy.
    cbn ; unfold idfun.
    use weqhomot.
    - exact (inv2_cell_to_disp_adjequiv_weq fx fy
             ∘ make_weq _ (HC (F x) (G x) fx fy))%weq.
    - intros p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence _ disp_inserter_bicat).
        * exact HB.
        * exact disp_inserter_bicat_univalent_2_1.
      + simpl.
        unfold inv2_cell_to_disp_adjequiv_left_adj.
        cbn -[psfunctor_id].
        rewrite !vassocl.
        rewrite id2_left.
        reflexivity.
  Qed.
End DisplayedInserter.
