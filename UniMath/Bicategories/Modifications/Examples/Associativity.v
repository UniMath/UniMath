(* ******************************************************************************* *)
(** Associativity laws are inverses
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
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section Associativity.
  Context {B₁ B₂ B₃ B₄: bicat}.
  Variable (F₁ : psfunctor B₁ B₂)
           (F₂ : psfunctor B₂ B₃)
           (F₃ : psfunctor B₃ B₄).

  Definition pstrans_lassociator_rassociator_data
    : invertible_modification_data
        (comp_trans
           (pstrans_lassociator F₁ F₂ F₃)
           (pstrans_rassociator F₁ F₂ F₃))
        (id_trans _).
  Proof.
    intros X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_lassociator_rassociator_is_modification
    : is_modification pstrans_lassociator_rassociator_data.
  Proof.
    intros X Y f ; cbn.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocl.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
    rewrite vcomp_lunitor.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Definition pstrans_lassociator_rassociator
    : invertible_modification
        (comp_trans
           (pstrans_lassociator F₁ F₂ F₃)
           (pstrans_rassociator F₁ F₂ F₃))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_lassociator_rassociator_data.
    - exact pstrans_lassociator_rassociator_is_modification.
  Defined.

  Definition pstrans_rassociator_lassociator_data
    : invertible_modification_data
        (comp_trans
           (pstrans_rassociator F₁ F₂ F₃)
           (pstrans_lassociator F₁ F₂ F₃))
        (id_trans _).
  Proof.
    intros X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_rassociator_lassociator_is_modification
    : is_modification pstrans_rassociator_lassociator_data.
  Proof.
    intros X Y f ; cbn.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocl.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
    rewrite vcomp_lunitor.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Definition pstrans_rassociator_lassociator
    : invertible_modification
        (comp_trans
           (pstrans_rassociator F₁ F₂ F₃)
           (pstrans_lassociator F₁ F₂ F₃))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_rassociator_lassociator_data.
    - exact pstrans_rassociator_lassociator_is_modification.
  Defined.
End Associativity.
