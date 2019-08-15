(* ******************************************************************************* *)
(** Associativity laws
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Local Open Scope cat.

Section Associativity.
  Context {B₁ B₂ B₃ B₄: bicat}.
  Variable (F₁ : psfunctor B₁ B₂)
           (F₂ : psfunctor B₂ B₃)
           (F₃ : psfunctor B₃ B₄).

  Definition pstrans_lassociator_data
    : pstrans_data
        (ps_comp F₃ (ps_comp F₂ F₁))
        (ps_comp (ps_comp F₃ F₂) F₁).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ _).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_lassociator_is_pstrans
    : is_pstrans pstrans_lassociator_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      apply maponpaths.
      rewrite rinvunitor_natural.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rinvunitor_natural.
          rewrite <- !rwhisker_hcomp.
          rewrite !vassocl.
          rewrite !rwhisker_vcomp.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rinvunitor_natural.
        rewrite !vassocl.
        rewrite <- rwhisker_hcomp.
        rewrite rwhisker_vcomp.
        apply idpath.
      }
      rewrite psfunctor_vcomp.
      rewrite rwhisker_vcomp.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite lunitor_triangle.
            rewrite !vassocl.
            rewrite rwhisker_hcomp.
            rewrite <- triangle_r_inv.
            rewrite <- lwhisker_hcomp.
            apply idpath.
          }
          rewrite !vassocl.
          rewrite lwhisker_vcomp.
          rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rinvunitor_triangle.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      etrans.
      {
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite !vassocr.
        rewrite <- vcomp_lunitor.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_lunitor.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite psfunctor_vcomp.
      apply idpath.
  Qed.

  Definition pstrans_lassociator
    : pstrans
        (ps_comp F₃ (ps_comp F₂ F₁))
        (ps_comp (ps_comp F₃ F₂) F₁).
  Proof.
    use make_pstrans.
    - exact pstrans_lassociator_data.
    - exact pstrans_lassociator_is_pstrans.
  Defined.

  Definition pstrans_rassociator_data
    : pstrans_data
        (ps_comp (ps_comp F₃ F₂) F₁)
        (ps_comp F₃ (ps_comp F₂ F₁)).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ _).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_rassociator_is_pstrans
    : is_pstrans pstrans_rassociator_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      apply maponpaths.
      rewrite rinvunitor_natural.
      etrans.
      {
        rewrite !vassocr.
        rewrite rinvunitor_natural.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply maponpaths.
      rewrite <- !rwhisker_hcomp.
      rewrite !rwhisker_vcomp.
      rewrite psfunctor_vcomp.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            rewrite lunitor_triangle.
            rewrite !vassocl.
            rewrite rwhisker_hcomp.
            rewrite <- triangle_r_inv.
            rewrite <- lwhisker_hcomp.
            apply idpath.
          }
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite lwhisker_vcomp.
          rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
          apply idpath.
        }
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rinvunitor_triangle.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite !rwhisker_vcomp.
      etrans.
      {
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite !vassocr.
        rewrite <- vcomp_lunitor.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_lunitor.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_lunitor.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite psfunctor_vcomp.
      apply idpath.
  Qed.

  Definition pstrans_rassociator
    : pstrans
        (ps_comp (ps_comp F₃ F₂) F₁)
        (ps_comp F₃ (ps_comp F₂ F₁)).
  Proof.
    use make_pstrans.
    - exact pstrans_rassociator_data.
    - exact pstrans_rassociator_is_pstrans.
  Defined.
End Associativity.
