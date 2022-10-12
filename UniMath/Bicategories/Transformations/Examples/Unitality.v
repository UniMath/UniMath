(* ******************************************************************************* *)
(** Unitality laws
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

Section LeftUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition lunitor_pstrans_data
    : pstrans_data (comp_psfunctor (id_psfunctor B₂) F) F.
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition lunitor_pstrans_is_pstrans
    : is_pstrans lunitor_pstrans_data.
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
      rewrite id2_left.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite rinvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite id2_left.
      rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      pose (triangle_r_inv (#F g) (#F f)) as p.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in p.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        exact (!p).
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition lunitor_pstrans
    : pstrans (comp_psfunctor (id_psfunctor B₂) F) F.
  Proof.
    use make_pstrans.
    - exact lunitor_pstrans_data.
    - exact lunitor_pstrans_is_pstrans.
  Defined.

  Definition linvunitor_pstrans_data
    : pstrans_data F (comp_psfunctor (id_psfunctor B₂) F).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition linvunitor_pstrans_is_pstrans
    : is_pstrans linvunitor_pstrans_data.
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
      rewrite id2_left.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite rinvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite id2_left.
      rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      pose (triangle_r_inv (#F g) (#F f)) as p.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in p.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        exact (!p).
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition linvunitor_pstrans
    : pstrans F (comp_psfunctor (id_psfunctor B₂) F).
  Proof.
    use make_pstrans.
    - exact linvunitor_pstrans_data.
    - exact linvunitor_pstrans_is_pstrans.
  Defined.
End LeftUnitality.

Section RightUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition runitor_pstrans_data
    : pstrans_data (comp_psfunctor F (id_psfunctor B₁)) F.
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition runitor_pstrans_is_pstrans
    : is_pstrans runitor_pstrans_data.
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
      rewrite psfunctor_id2, id2_right.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite rinvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite psfunctor_id2, id2_right.
      rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      pose (triangle_r_inv (#F g) (#F f)) as p.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in p.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        exact (!p).
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition runitor_pstrans
    : pstrans (comp_psfunctor F (id_psfunctor B₁)) F.
  Proof.
    use make_pstrans.
    - exact runitor_pstrans_data.
    - exact runitor_pstrans_is_pstrans.
  Defined.

  Definition rinvunitor_pstrans_data
    : pstrans_data F (comp_psfunctor F (id_psfunctor B₁)).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition rinvunitor_pstrans_is_pstrans
    : is_pstrans rinvunitor_pstrans_data.
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
      rewrite psfunctor_id2, id2_right.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite rinvunitor_natural.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite rwhisker_hcomp.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite psfunctor_id2, id2_right.
      rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      pose (triangle_r_inv (#F g) (#F f)) as p.
      rewrite <- lwhisker_hcomp, <- rwhisker_hcomp in p.
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        exact (!p).
      }
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
  Qed.

  Definition rinvunitor_pstrans
    : pstrans F (comp_psfunctor F (id_psfunctor B₁)).
  Proof.
    use make_pstrans.
    - exact rinvunitor_pstrans_data.
    - exact rinvunitor_pstrans_is_pstrans.
  Defined.
End RightUnitality.
