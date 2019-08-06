(* ******************************************************************************* *)
(** Unitality laws are inverses
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section LeftUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition pstrans_lunitor_linvunitor_data
    : invertible_modification_data
        (comp_trans (pstrans_lunitor F) (pstrans_linvunitor F))
        (id_trans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_lunitor_linvunitor_is_modification
    : is_modification pstrans_lunitor_linvunitor_data.
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

  Definition pstrans_lunitor_linvunitor
    : invertible_modification
        (comp_trans (pstrans_lunitor F) (pstrans_linvunitor F))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_lunitor_linvunitor_data.
    - exact pstrans_lunitor_linvunitor_is_modification.
  Defined.

  Definition pstrans_linvunitor_lunitor_data
    : invertible_modification_data
        (comp_trans (pstrans_linvunitor F) (pstrans_lunitor F))
        (id_trans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_linvunitor_lunitor_is_modification
    : is_modification pstrans_linvunitor_lunitor_data.
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

  Definition pstrans_linvunitor_lunitor
    : invertible_modification
        (comp_trans (pstrans_linvunitor F) (pstrans_lunitor F))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_linvunitor_lunitor_data.
    - exact pstrans_linvunitor_lunitor_is_modification.
  Defined.
End LeftUnitality.

Section RightUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition pstrans_runitor_rinvunitor_data
    : invertible_modification_data
        (comp_trans (pstrans_runitor F) (pstrans_rinvunitor F))
        (id_trans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_runitor_rinvunitor_is_modification
    : is_modification pstrans_runitor_rinvunitor_data.
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

  Definition pstrans_runitor_rinvunitor
    : invertible_modification
        (comp_trans (pstrans_runitor F) (pstrans_rinvunitor F))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_runitor_rinvunitor_data.
    - exact pstrans_runitor_rinvunitor_is_modification.
  Defined.

  Definition pstrans_rinvunitor_runitor_data
    : invertible_modification_data
        (comp_trans (pstrans_rinvunitor F) (pstrans_runitor F))
        (id_trans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition pstrans_rinvunitor_runitor_is_modification
    : is_modification pstrans_rinvunitor_runitor_data.
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

  Definition pstrans_rinvunitor_runitor
    : invertible_modification
        (comp_trans (pstrans_rinvunitor F) (pstrans_runitor F))
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - exact pstrans_rinvunitor_runitor_data.
    - exact pstrans_rinvunitor_runitor_is_modification.
  Defined.
End RightUnitality.
