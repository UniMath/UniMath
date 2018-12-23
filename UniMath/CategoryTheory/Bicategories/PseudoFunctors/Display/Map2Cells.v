(** The second layer of the construction of the bicategory of pseudofunctors consists of three parts.
    First part: we add an action of 1-cells.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
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

Section Map2Cells.
  Variable (C D : bicat).

  Definition map2cells_disp_cat_data
    : disp_cat_ob_mor (map1cells C D).
  Proof.
    use tpair.
    - exact (λ F, ∏ (X Y : C) (f g : X --> Y), f ==> g → Fmor F f ==> Fmor F g).
    - exact (λ F G F₂ G₂ η, ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
             (ηobj η X ◃ G₂ X Y f g α) • ηmor η g
             =
             ηmor η f • (F₂ X Y f g α ▹ ηobj η Y)) ; cbn in *.
  Defined.

  Definition map2cells_disp_cat_laws
    : disp_cat_id_comp (map1cells C D) map2cells_disp_cat_data.
  Proof.
    split.
    - intros F F₂ X Y f g α ; cbn in *.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros F G H η ε F₂ G₂ H₂ η₂ ε₂ X Y f g α ; cbn in *.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite ε₂.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite η₂.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      reflexivity.
  Qed.

  Definition map2cells_disp_cat
    : disp_bicat (map1cells C D).
  Proof.
    use disp_cell_unit_bicat.
    use tpair.
    - exact map2cells_disp_cat_data.
    - exact map2cells_disp_cat_laws.
  Defined.

  Definition map2cells_is_disp_univalent_2_1
    : disp_locally_univalent map2cells_disp_cat.
  Proof.
    apply disp_cell_unit_bicat_locally_univalent.
    intros F G η F₂ G₂ ; simpl in *.
    repeat (apply impred ; intro).
    apply D.
  Defined.

  Definition map2cells_is_disp_univalent_2_0
             (HD_2_1 : is_univalent_2_1 D)
    : disp_univalent_2_0 map2cells_disp_cat.
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
      apply funextsec ; intro f.
      apply funextsec ; intro g.
      apply funextsec ; intro α.
      specialize (η₁ X Y f g α).
      specialize (η₂ X Y f g α).
      rewrite !vassocr in η₁.
      rewrite vcomp_lunitor in η₁.
      rewrite !vassocl in η₁.
      rewrite rinvunitor_natural in η₁.
      rewrite <- rwhisker_hcomp in η₁.
      rewrite !vassocr in η₁.
      apply rwhisker_id_inj.
      use (vcomp_lcancel (lunitor _ • rinvunitor _)).
      { is_iso. }
      exact (!η₁).
  Defined.
End Map2Cells.