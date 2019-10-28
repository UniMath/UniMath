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

  Definition lassociator_rassociator_pstrans_data
    : invertible_modification_data
        (comp_pstrans
           (lassociator_pstrans F₁ F₂ F₃)
           (rassociator_pstrans F₁ F₂ F₃))
        (id_pstrans _).
  Proof.
    intros X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition lassociator_rassociator_pstrans_modification
    : is_modification lassociator_rassociator_pstrans_data.
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

  Definition lassociator_rassociator_pstrans
    : invertible_modification
        (comp_pstrans
           (lassociator_pstrans F₁ F₂ F₃)
           (rassociator_pstrans F₁ F₂ F₃))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact lassociator_rassociator_pstrans_data.
    - exact lassociator_rassociator_pstrans_modification.
  Defined.

  Definition rassociator_lassociator_pstrans_data
    : invertible_modification_data
        (comp_pstrans
           (rassociator_pstrans F₁ F₂ F₃)
           (lassociator_pstrans F₁ F₂ F₃))
        (id_pstrans _).
  Proof.
    intros X.
    use make_invertible_2cell.
    - exact (lunitor _).
    - is_iso.
  Defined.

  Definition rassociator_lassociator_pstrans_is_modification
    : is_modification rassociator_lassociator_pstrans_data.
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

  Definition rassociator_lassociator_pstrans
    : invertible_modification
        (comp_pstrans
           (rassociator_pstrans F₁ F₂ F₃)
           (lassociator_pstrans F₁ F₂ F₃))
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact rassociator_lassociator_pstrans_data.
    - exact rassociator_lassociator_pstrans_is_modification.
  Defined.
End Associativity.
