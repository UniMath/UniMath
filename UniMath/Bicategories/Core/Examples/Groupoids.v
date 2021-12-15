(* ******************************************************************************* *)
(** Groupoids
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Local Open Scope cat.

Definition grpds : bicat
  := fullsubbicat bicat_of_univ_cats (λ X, is_pregroupoid (pr1 X)).

Definition grpds_univalent
  : is_univalent_2 grpds.
Proof.
  apply is_univalent_2_fullsubbicat.
  - apply univalent_cat_is_univalent_2.
  - intro.
    apply isaprop_is_pregroupoid.
Defined.

Definition grpd_bicat_is_invertible_2cell
           {G₁ G₂ : grpds}
           {F₁ F₂ : G₁ --> G₂}
           (α : F₁ ==> F₂)
  : is_invertible_2cell α.
Proof.
  use make_is_invertible_2cell.
  - refine (_ ,, tt).
    use make_nat_trans.
    + intros X.
      exact (inv_from_iso (_ ,, pr2 G₂ _ _ (pr11 α X))).
    + abstract
        (intros X Y f ; cbn ;
         refine (!_) ;
         apply iso_inv_on_right ;
         rewrite !assoc ;
         apply iso_inv_on_left ;
         simpl ;
         exact (!(pr21 α X Y f))).
  - abstract
      (apply subtypePath ; try (intro ; apply isapropunit)
       ; apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (iso_inv_after_iso (_ ,, _))).
  - abstract
      (apply subtypePath ; try (intro ; apply isapropunit)
       ; apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (iso_after_iso_inv (_ ,, _))).
Defined.
