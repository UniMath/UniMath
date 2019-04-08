(** The second layer of the construction of the bicategory of pseudofunctors consists of three parts.
    Second part: we add a 2-cell witnessing preservation of the identity.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section Identitor.
  Variable (C D : bicat).

  Definition identitor_disp_cat_data
    : disp_cat_ob_mor (map1cells C D).
  Proof.
    use tpair.
    - exact (λ F, ∏ (X : C), id₁ (Fobj F X) ==> Fmor F (id₁ X)).
    - exact (λ F G Fid Gid η,
             ∏ (X : C),
             (ηobj η X ◃ Gid X)
               • ηmor η (id₁ X)
             =
             (runitor (ηobj η X))
               • linvunitor (ηobj η X)
               • (Fid X ▹ ηobj η X)).
  Defined.

  Definition identitor_disp_id_comp
    : disp_cat_id_comp (map1cells C D) identitor_disp_cat_data.
  Proof.
    split.
    - intros F Fid X ; cbn in *.
      rewrite !vassocr.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_linvunitor, id2_left.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite !vassocr.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor, id2_left.
      rewrite rwhisker_hcomp.
      reflexivity.
    - intros F G H Fid Gid Hid η ε ηid εid X ; cbn in *.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite εid.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite ηid.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite linvunitor_assoc.
      reflexivity.
  Qed.

  Definition identitor_disp_cat
    : disp_bicat (map1cells C D).
  Proof.
    use disp_cell_unit_bicat.
    use tpair.
    - exact identitor_disp_cat_data.
    - exact identitor_disp_id_comp.
  Defined.

  Definition identitor_is_disp_univalent_2_1
    : disp_univalent_2_1 identitor_disp_cat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intros F G η Fid Gid ; simpl in *.
    apply impred ; intro.
    apply D.
  Defined.

  Definition identitor_is_disp_univalent_2_0
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2_0 identitor_disp_cat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - apply map1cells_is_univalent_2_1.
      exact HD_2_1.
    - intros ; simpl.
      apply impred ; intro.
      apply D.
    - intro ; cbn.
      apply impred_isaset ; intro.
      apply D.
    - intros F Fid Fid' η ; cbn in *.
      apply funextsec ; intro X.
      induction η as [η₁ η₂].
      specialize (η₁ X).
      specialize (η₂ X).
      rewrite !vassocr in η₁.
      rewrite vcomp_lunitor in η₁.
      rewrite !vassocl in η₁.
      rewrite rinvunitor_natural in η₁.
      rewrite <- rwhisker_hcomp in η₁.
      rewrite lunitor_runitor_identity, lunitor_V_id_is_left_unit_V_id in η₁.
      rewrite !vassocr in η₁.
      rewrite !runitor_rinvunitor, !id2_left in η₁.
      apply rwhisker_id_inj.
      exact (!η₁).
  Defined.

  Definition identitor_is_disp_univalent_2
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2 identitor_disp_cat.
  Proof.
    split.
    - apply identitor_is_disp_univalent_2_0; assumption.
    - exact identitor_is_disp_univalent_2_1.
  Defined.

End Identitor.
