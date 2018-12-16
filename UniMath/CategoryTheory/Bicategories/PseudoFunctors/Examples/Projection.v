(* ******************************************************************************* *)
(** The projection of the total bicategory of some displayed category to the base
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Projection.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Definition pr1_psfunctor_data : psfunctor_data (total_bicat D) C.
  Proof.
    use mk_psfunctor_data.
    - exact pr1.
    - exact (λ _ _, pr1).
    - exact (λ _ _ _ _, pr1).
    - exact (λ a, id₂(id₁ (pr1 a))).
    - exact (λ _ _ _ f g, id₂ (pr1 f · pr1 g)).
  Defined.

  Definition pr1_psfunctor_laws : psfunctor_laws pr1_psfunctor_data.
  Proof.
    repeat split; intro a; intros; cbn.
    - rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite id2_left.
      apply idpath.
    - rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite id2_left.
      apply idpath.
    - rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      apply idpath.
    - rewrite id2_right.
      rewrite id2_left.
      apply idpath.
    - rewrite id2_left.
      rewrite id2_right.
      apply idpath.
    - is_iso.
    - is_iso.
  Qed.

  Definition pr1_laxfunctor : psfunctor (total_bicat D) C
    := _ ,, pr1_psfunctor_laws.
End Projection.