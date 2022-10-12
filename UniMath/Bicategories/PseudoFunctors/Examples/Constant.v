(** Constant pseudofunctor *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.Notations.

Local Open Scope cat.

Section Constant.
  Context (B₁ : bicat)
          {B₂ : bicat}
          (Y : B₂).

  Definition constant_data : psfunctor_data B₁ B₂.
  Proof.
    use make_psfunctor_data.
    - exact (λ _, Y).
    - exact (λ _ _ _, id₁ Y).
    - exact (λ _ _ _ _ _, id₂ (id₁ Y)).
    - exact (λ _, id₂ (id₁ Y)).
    - exact (λ _ _ _ _ _, lunitor (id₁ Y)).
  Defined.

  Definition constant_laws : psfunctor_laws constant_data.
  Proof.
    repeat split.
    - intros a b f g h α β ; cbn.
      rewrite id2_left.
      apply idpath.
    - intros a b f ; cbn.
      rewrite id2_rwhisker, id2_left, id2_right.
      apply idpath.
    - intros a b f ; cbn.
      rewrite lwhisker_id2, id2_left, id2_right, runitor_lunitor_identity.
      apply idpath.
    - intros a b c d f g h ; cbn.
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite lunitor_is_lunitor_lwhisker.
      apply idpath.
    - intros a b c f g h α ; cbn.
      rewrite lwhisker_id2, id2_left, id2_right.
      apply idpath.
    - intros a b c f g h α ; cbn.
      rewrite id2_rwhisker, id2_left, id2_right.
      apply idpath.
  Qed.

  Definition constant_invertible_cells
    : invertible_cells constant_data.
  Proof.
    split.
    - intro a ; cbn.
      is_iso.
    - intros a b c f g ; cbn.
      is_iso.
  Defined.

  Definition constant : psfunctor B₁ B₂.
  Proof.
    use make_psfunctor.
    - exact constant_data.
    - exact constant_laws.
    - exact constant_invertible_cells.
  Defined.
End Constant.
