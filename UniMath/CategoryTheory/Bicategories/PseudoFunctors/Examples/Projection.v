(* ******************************************************************************* *)
(** The projection of the total bicategory of some displayed category to the base
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Projection.
  Context {C : bicat}.
  Variable (D : disp_bicat C).

  Definition strict_pr1_psfunctor_data : strict_psfunctor_data (total_bicat D) C.
  Proof.
    use make_strict_psfunctor_data.
    - exact pr1.
    - exact (λ _ _, pr1).
    - exact (λ _ _ _ _, pr1).
    - exact (λ a, idpath _).
    - exact (λ _ _ _ f g, idpath _).
  Defined.

  Definition strict_pr1_psfunctor_laws : is_strict_psfunctor strict_pr1_psfunctor_data.
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
  Qed.

  Definition strict_pr1_psfunctor : strict_psfunctor (total_bicat D) C.
  Proof.
    use make_strict_psfunctor.
    - exact strict_pr1_psfunctor_data.
    - exact strict_pr1_psfunctor_laws.
  Defined.

  Definition pr1_psfunctor : psfunctor (total_bicat D) C
    := strict_psfunctor_to_psfunctor_map _ _ strict_pr1_psfunctor.
End Projection.
