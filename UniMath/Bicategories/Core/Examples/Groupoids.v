(* ******************************************************************************* *)
(** Groupoids
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
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

Definition locally_groupoid_grpds
  : locally_groupoid grpds.
Proof.
  intros G₁ G₂ F₁ F₂ α.
  use make_is_invertible_2cell.
  - refine (_ ,, tt).
    use make_nat_trans.
    + exact (λ x, inv_from_z_iso (_ ,, pr2 G₂ _ _ (pr11 α x))).
    + abstract
        (intros x y f ; cbn ;
         refine (!_) ;
         apply z_iso_inv_on_right ;
         rewrite !assoc ;
         apply z_iso_inv_on_left ;
         simpl ;
         exact (!(pr21 α x y f))).
  - abstract
      (apply subtypePath ; try (intro ; apply isapropunit)
       ; apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (z_iso_inv_after_z_iso (_ ,, _))).
  - abstract
      (apply subtypePath ; try (intro ; apply isapropunit)
       ; apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (z_iso_after_z_iso_inv (_ ,, _))).
Defined.

Definition grpds_2cell_to_nat_z_iso
           {G₁ G₂ : grpds}
           {F₁ F₂ : G₁ --> G₂}
           (α : F₁ ==> F₂)
  : nat_z_iso (pr1 F₁) (pr1 F₂).
Proof.
  use make_nat_z_iso.
  - exact (pr1 α).
  - intros x.
    exact (pr2 G₂ (pr11 F₁ x) (pr11 F₂ x) (pr11 α x)).
Defined.
