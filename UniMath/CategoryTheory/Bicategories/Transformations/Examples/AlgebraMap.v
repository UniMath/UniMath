(* ******************************************************************************* *)
(** Algebra map as pseudotransformation
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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.

Definition var
           {C : bicat}
           (F S : psfunctor C C)
  : pstrans
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         S (pr1_psfunctor (disp_alg_bicat F)))
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         S (pr1_psfunctor (disp_alg_bicat F)))
  := id₁ _.

Definition alg_map_data
           {C : bicat}
           (F : psfunctor C C)
  : pstrans_data
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         F (pr1_psfunctor (disp_alg_bicat F)))
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         (ps_id_functor C) (pr1_psfunctor (disp_alg_bicat F))).
Proof.
  use make_pstrans_data.
  - intros X ; cbn in *.
    exact (pr2 X).
  - intros X Y f ; cbn in *.
    exact (pr2 f).
Defined.

Definition alg_map_data_is_pstrans
           {C : bicat}
           (F : psfunctor C C)
  : is_pstrans (alg_map_data F).
Proof.
  repeat split ; cbn.
  - intros X Y f g α.
    apply α.
  - intros.
    rewrite !id2_left, lwhisker_id2, psfunctor_id2.
    rewrite !id2_left, !id2_right.
    reflexivity.
  - intros.
    rewrite !id2_left, lwhisker_id2, psfunctor_id2.
    rewrite !id2_left, !id2_right.
    reflexivity.
Qed.

Definition alg_map
           {C : bicat}
           (F : psfunctor C C)
  : pstrans
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         F (pr1_psfunctor (disp_alg_bicat F)))
      (@ps_comp
         (total_bicat (disp_alg_bicat F)) C C
         (ps_id_functor C) (pr1_psfunctor (disp_alg_bicat F))).
Proof.
  use make_pstrans.
  - exact (alg_map_data F).
  - exact (alg_map_data_is_pstrans F).
Defined.
