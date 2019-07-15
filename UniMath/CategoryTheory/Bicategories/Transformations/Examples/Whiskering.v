(* ******************************************************************************* *)
(** Left whiskering
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.

Local Open Scope cat.

Section LeftWhisker.
  Context {B₁ B₂ B₃ : bicat}
          {F₁ F₂ : psfunctor B₁ B₂}.
  Variable (G : psfunctor B₂ B₃)
           (η : pstrans F₁ F₂).

  Definition left_whisker_data
    : pstrans_data (ps_comp G F₁) (ps_comp G F₂).
  Proof.
    use make_pstrans_data.
    - exact (λ X, #G (η X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact ((psfunctor_comp G (η X) (#F₂ f))
                 • ##G (psnaturality_of η f)
                 • (psfunctor_comp G (#F₁ f) (η Y))^-1).
      + is_iso.
        * apply psfunctor_comp.
        * apply psfunctor_is_iso.
  Defined.

  Definition left_whisker_is_pstrans
    : is_pstrans left_whisker_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      rewrite !vassocr.
      rewrite <- psfunctor_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- psfunctor_vcomp.
      rewrite psnaturality_natural.
      rewrite psfunctor_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      cbn.
      rewrite psfunctor_rwhisker.
      apply idpath.
    - intros X ; cbn.
      rewrite psfunctor_runitor.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite <- psfunctor_rwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        exact (!(psfunctor_linvunitor G (η X))).
      }
      rewrite <- !psfunctor_vcomp.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        exact (!(pstrans_id η X)).
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite <- psfunctor_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite psfunctor_vcomp.
      apply idpath.
    - intros X Y Z f g.
      cbn -[psfunctor_comp].
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply ps_comp_psfunctor_comp.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply ps_comp_psfunctor_comp.
      }
      rewrite !vassocl.
      refine (!_).
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite <- psfunctor_lwhisker.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite <- psfunctor_vcomp.
        rewrite pstrans_comp.
        rewrite !psfunctor_vcomp.
        rewrite !vassocr.
        do 5 apply maponpaths_2.
        apply psfunctor_lassociator.
      }
      rewrite !vassocl.
      do 2 apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite psfunctor_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn -[psfunctor_comp].
      etrans.
      {
        rewrite !vassocr.
        rewrite psfunctor_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      do 2 apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite psfunctor_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn -[psfunctor_comp].
      etrans.
      {
        rewrite !vassocr.
        rewrite psfunctor_lassociator.
        rewrite !vassocl.
        apply idpath.
      }
      do 2 apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp.
      { is_iso. }
      cbn -[psfunctor_comp].
      rewrite psfunctor_rwhisker.
      apply idpath.
  Qed.

  Definition left_whisker
    : pstrans (ps_comp G F₁) (ps_comp G F₂).
  Proof.
    use make_pstrans.
    - exact left_whisker_data.
    - exact left_whisker_is_pstrans.
  Defined.
End LeftWhisker.

Section RightWhisker.
  Context {B₁ B₂ B₃ : bicat}
          {G₁ G₂ : psfunctor B₂ B₃}.
  Variable (F : psfunctor B₁ B₂)
           (η : pstrans G₁ G₂).

  Definition right_whisker_data
    : pstrans_data (ps_comp G₁ F) (ps_comp G₂ F).
  Proof.
    use make_pstrans_data.
    - exact (λ X, η (F X)).
    - exact (λ X Y f, psnaturality_of η (#F f)).
  Defined.

  Definition right_whisker_is_pstrans
    : is_pstrans right_whisker_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      exact (psnaturality_natural η _ _ _ _ (##F α)).
    - intros X ; cbn.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!(pstrans_id η (F X))).
      }
      cbn.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite psnaturality_natural.
      apply idpath.
    - intros X Y Z f g ; cbn.
      etrans.
      {
        rewrite <- lwhisker_vcomp.
        rewrite !vassocl.
        rewrite psnaturality_natural.
        rewrite !vassocr.
        apply maponpaths_2.
        exact (pstrans_comp η (#F f) (#F g)).
      }
      rewrite !vassocl.
      do 5 apply maponpaths.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Definition right_whisker
    : pstrans (ps_comp G₁ F) (ps_comp G₂ F).
  Proof.
    use make_pstrans.
    - exact right_whisker_data.
    - exact right_whisker_is_pstrans.
  Defined.
End RightWhisker.

Notation "G ◅ η" := (left_whisker G η).
Notation "η ▻ F" := (right_whisker F η).
