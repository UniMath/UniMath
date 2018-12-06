Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.LaxTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.

Local Open Scope cat.

Section IdentityTransformation.
  Context {C D : bicat}.
  Variable (F : psfunctor C D).

  Definition id_trans_data : laxtrans_data F F.
  Proof.
    use mk_laxtrans_data.
    - exact (λ X, id₁ (F X)).
    - exact (λ X Y f, lunitor (#F f) • rinvunitor (#F f)).
  Defined.

  Definition id_trans_laws
    : is_laxtrans id_trans_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros X ; simpl in *.
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
    - intros X Y Z f g ; simpl in *.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_hcomp.
      rewrite triangle_l.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
  Qed.

  Definition id_laxtrans : laxtrans F F
    := mk_laxtrans id_trans_data id_trans_laws.

  Definition id_laxtrans_is_pseudo
    : is_pseudo_trans id_laxtrans.
  Proof.
    intros X Y f ; cbn.
    is_iso.
  Defined.

  Definition id_trans : pstrans F F
    := mk_pstrans id_laxtrans id_laxtrans_is_pseudo.
End IdentityTransformation.
