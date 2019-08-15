(** The second layer of the construction of the bicategory of pseudofunctors consists of three parts.
    Third part: we add a 2-cell witnessing preservation of composition.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section Compositor.
  Variable (C D : bicat).

  Definition compositor_disp_cat_data
    : disp_cat_ob_mor (map1cells C D).
  Proof.
    use tpair.
    - exact (λ F,
             ∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
             Fmor F f · Fmor F g ==> Fmor F (f · g)).
    - exact (λ F G Fcomp Gcomp η,
             ∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
             (ηobj η X ◃ Gcomp X Y Z f g)
               • ηmor η (f · g)
             =
             (lassociator (ηobj η X) (Fmor G f) (Fmor G g))
               • (ηmor η f ▹ (Fmor G g))
               • rassociator (Fmor F f) (ηobj η Y) (Fmor G g)
               • (Fmor F f ◃ ηmor η g)
               • lassociator (Fmor F f) (Fmor F g) (ηobj η Z)
               • (Fcomp X Y Z f g ▹ ηobj η Z)).
  Defined.

  Definition compositor_disp_cat_id_comp
    : disp_cat_id_comp (map1cells C D) compositor_disp_cat_data.
  Proof.
    split.
    - intros F Fcomp X Y Z f g ; cbn in *.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_hcomp.
      rewrite triangle_l.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros F₁ F₂ F₃ η ε Fcomp₁ Fcomp₂ Fcomp₃ ηcomp εcomp X Y Z f g ; cbn in *.
      specialize (ηcomp X Y Z f g).
      specialize (εcomp X Y Z f g).
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite lwhisker_vcomp.
        apply maponpaths.
        do 3 apply maponpaths_2.
        apply maponpaths.
        apply εcomp.
      }
      clear εcomp.
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        do 5 (apply maponpaths).
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        apply maponpaths_2.
        rewrite !vassocl.
        apply maponpaths.
        rewrite rwhisker_vcomp.
        apply maponpaths.
        apply ηcomp.
      }
      clear ηcomp.
      rewrite !vassocl.
      symmetry.
      etrans.
      {
        rewrite !vassocr.
        do 12 (apply maponpaths_2).
        rewrite rwhisker_hcomp.
        rewrite !vassocl, <- pentagon_2.
        rewrite <- lwhisker_hcomp.
        reflexivity.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        do 11 (apply maponpaths_2).
        symmetry.
        apply rwhisker_lwhisker.
      }
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 10 (apply maponpaths_2).
        rewrite !vassocl.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        apply pentagon.
      }
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      symmetry.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 6 apply (maponpaths_2).
        rewrite vassocl.
        symmetry.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        apply pentagon.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 5 (apply maponpaths_2).
        rewrite rwhisker_rwhisker.
        reflexivity.
      }
      rewrite !vassocl.
      symmetry.
      etrans.
      {
        rewrite !vassocr.
        do 9 (apply maponpaths_2).
        apply rwhisker_rwhisker.
      }
      etrans.
      {
        do 7 (apply maponpaths_2).
        rewrite !vassocl.
        apply maponpaths.
        rewrite rwhisker_hcomp.
        rewrite <- inverse_pentagon_4.
        rewrite <- lwhisker_hcomp.
        reflexivity.
      }
      etrans.
      {
        do 6 (apply maponpaths_2).
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite lassociator_rassociator, lwhisker_id2, id2_right.
        reflexivity.
      }
      symmetry.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        reflexivity.
      }
      rewrite !vassocl.
      apply maponpaths.
      symmetry.
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 4 (apply maponpaths_2).
        rewrite inverse_pentagon.
        rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator, lwhisker_id2, id2_right.
        reflexivity.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        symmetry.
        apply inverse_pentagon_2.
      }
      rewrite !vassocl, <- rwhisker_hcomp.
      do 2 apply maponpaths.
      symmetry.
      apply rwhisker_rwhisker_alt.
  Qed.

  Definition compositor_disp_cat
    : disp_bicat (map1cells C D).
  Proof.
    use disp_cell_unit_bicat.
    use tpair.
    - exact compositor_disp_cat_data.
    - exact compositor_disp_cat_id_comp.
  Defined.

  Definition compositor_is_disp_univalent_2_1
    : disp_univalent_2_1 compositor_disp_cat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intros F G η Fcomp Gcomp ; simpl in *.
    repeat (apply impred ; intro).
    apply D.
  Defined.

  Definition compositor_is_disp_univalent_2_0
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2_0 compositor_disp_cat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - apply map1cells_is_univalent_2_1.
      exact HD_2_1.
    - intros ; simpl.
      repeat (apply impred ; intro).
      apply D.
    - intro ; cbn.
      repeat (apply impred_isaset ; intro).
      apply D.
    - intros F F₂ F₂' η ; cbn in *.
      induction η as [η₁ η₂].
      apply funextsec ; intro X.
      apply funextsec ; intro Y.
      apply funextsec ; intro Z.
      apply funextsec ; intro f.
      apply funextsec ; intro g.
      specialize (η₁ X Y Z f g).
      specialize (η₂ X Y Z f g).
      rewrite !vassocr in η₁.
      rewrite vcomp_lunitor in η₁.
      rewrite !vassocl in η₁.
      rewrite rinvunitor_natural in η₁.
      rewrite <- rwhisker_hcomp in η₁.
      rewrite !vassocr in η₁.
      apply rwhisker_id_inj.
      use (vcomp_lcancel (lunitor _ • rinvunitor _)).
      { is_iso. }
      refine (_ @ !η₁).
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      apply maponpaths_2.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- !lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      reflexivity.
  Defined.

  Definition compositor_is_disp_univalent_2
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2 compositor_disp_cat.
  Proof.
    split.
    - apply compositor_is_disp_univalent_2_0; assumption.
    - exact compositor_is_disp_univalent_2_1.
  Defined.

End Compositor.
