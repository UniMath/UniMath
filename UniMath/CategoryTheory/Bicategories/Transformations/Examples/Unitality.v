(* ******************************************************************************* *)
(** Unitality laws
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

Local Open Scope cat.

Section LeftUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition pstrans_lunitor_data
    : pstrans_data (ps_comp (ps_id_functor B₂) F) F.
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_lunitor_is_pstrans
    : is_pstrans pstrans_lunitor_data.
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

  Definition pstrans_lunitor
    : pstrans (ps_comp (ps_id_functor B₂) F) F.
  Proof.
    use make_pstrans.
    - exact pstrans_lunitor_data.
    - exact pstrans_lunitor_is_pstrans.
  Defined.

  Definition pstrans_linvunitor_data
    : pstrans_data F (ps_comp (ps_id_functor B₂) F).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_linvunitor_is_pstrans
    : is_pstrans pstrans_linvunitor_data.
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

  Definition pstrans_linvunitor
    : pstrans F (ps_comp (ps_id_functor B₂) F).
  Proof.
    use make_pstrans.
    - exact pstrans_linvunitor_data.
    - exact pstrans_linvunitor_is_pstrans.
  Defined.
End LeftUnitality.

Section RightUnitality.
  Context {B₁ B₂ : bicat}.
  Variable (F : psfunctor B₁ B₂).

  Definition pstrans_runitor_data
    : pstrans_data (ps_comp F (ps_id_functor B₁)) F.
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_runitor_is_pstrans
    : is_pstrans pstrans_runitor_data.
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

  Definition pstrans_runitor
    : pstrans (ps_comp F (ps_id_functor B₁)) F.
  Proof.
    use make_pstrans.
    - exact pstrans_runitor_data.
    - exact pstrans_runitor_is_pstrans.
  Defined.

  Definition pstrans_rinvunitor_data
    : pstrans_data F (ps_comp F (ps_id_functor B₁)).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - intros X Y f ; cbn.
      use make_invertible_2cell.
      + exact (lunitor _ • rinvunitor _).
      + is_iso.
  Defined.

  Definition pstrans_rinvunitor_is_pstrans
    : is_pstrans pstrans_rinvunitor_data.
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

  Definition pstrans_rinvunitor
    : pstrans F (ps_comp F (ps_id_functor B₁)).
  Proof.
    use make_pstrans.
    - exact pstrans_rinvunitor_data.
    - exact pstrans_rinvunitor_is_pstrans.
  Defined.
End RightUnitality.
