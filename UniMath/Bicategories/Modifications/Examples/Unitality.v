(* ******************************************************************************* *)
(** Unitality laws are inverses
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
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section LeftUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition lunitor_linvunitor_pstrans_data
    : invertible_modification_data
        (comp_pstrans (lunitor_pstrans F) (linvunitor_pstrans F))
        (id_pstrans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition lunitor_linvunitor_pstrans_is_modification
    : is_modification lunitor_linvunitor_pstrans_data.
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

  Definition lunitor_linvunitor_pstrans
    : invertible_modification
        (comp_pstrans (lunitor_pstrans F) (linvunitor_pstrans F))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact lunitor_linvunitor_pstrans_data.
    - exact lunitor_linvunitor_pstrans_is_modification.
  Defined.

  Definition linvunitor_lunitor_pstrans_data
    : invertible_modification_data
        (comp_pstrans (linvunitor_pstrans F) (lunitor_pstrans F))
        (id_pstrans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition linvunitor_lunitor_pstrans_is_modification
    : is_modification linvunitor_lunitor_pstrans_data.
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

  Definition linvunitor_lunitor_pstrans
    : invertible_modification
        (comp_pstrans (linvunitor_pstrans F) (lunitor_pstrans F))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact linvunitor_lunitor_pstrans_data.
    - exact linvunitor_lunitor_pstrans_is_modification.
  Defined.
End LeftUnitality.

Section RightUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition runitor_rinvunitor_pstrans_data
    : invertible_modification_data
        (comp_pstrans (runitor_pstrans F) (rinvunitor_pstrans F))
        (id_pstrans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition runitor_rinvunitor_pstrans_is_modification
    : is_modification runitor_rinvunitor_pstrans_data.
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

  Definition runitor_rinvunitor_pstrans
    : invertible_modification
        (comp_pstrans (runitor_pstrans F) (rinvunitor_pstrans F))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact runitor_rinvunitor_pstrans_data.
    - exact runitor_rinvunitor_pstrans_is_modification.
  Defined.

  Definition rinvunitor_runitor_pstrans_data
    : invertible_modification_data
        (comp_pstrans (rinvunitor_pstrans F) (runitor_pstrans F))
        (id_pstrans _).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition rinvunitor_runitor_pstrans_is_modification
    : is_modification rinvunitor_runitor_pstrans_data.
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

  Definition rinvunitor_runitor_pstrans
    : invertible_modification
        (comp_pstrans (rinvunitor_pstrans F) (runitor_pstrans F))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact rinvunitor_runitor_pstrans_data.
    - exact rinvunitor_runitor_pstrans_is_modification.
  Defined.
End RightUnitality.
