(*********************************************************************

 Cores in a bicategory

 The core of a category is the subgroupoid consisting of only the
 isomorphisms. This construction can be specified in arbitrary
 bicategories.
 The definition we use here, is inspired by

 https://ncatlab.org/nlab/show/core+in+a+2-category

 Contents
 1. Groupoidal objects
 2. Pseudofunctor from groupoids
 3. Having cores

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Eso.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.BicatOfInvertibles.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.

Local Open Scope cat.

(**
 1. Groupoidal objects
 *)
Definition groupoidal
           {B : bicat}
           (x : B)
  : UU
  := ∏ (w : B)
       (f g : w --> x)
       (α : f ==> g),
     is_invertible_2cell α.

Definition isaprop_groupoidal
           {B : bicat}
           (x : B)
  : isaprop (groupoidal x).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_invertible_2cell.
Qed.

Definition bicat_of_groupoidal
           (B : bicat)
  : bicat
  := fullsubbicat B groupoidal.

Definition is_univalent_2_1_bicat_of_groupoidal
           {B : bicat}
           (HB_2_1 : is_univalent_2_1 B)
  : is_univalent_2_1 (bicat_of_groupoidal B).
Proof.
  apply is_univalent_2_1_fullsubbicat.
  exact HB_2_1.
Defined.

Definition is_univalent_2_0_bicat_of_groupoidal
           {B : bicat}
           (HB_2 : is_univalent_2 B)
  : is_univalent_2_0 (bicat_of_groupoidal B).
Proof.
  apply is_univalent_2_0_fullsubbicat.
  - exact HB_2.
  - exact isaprop_groupoidal.
Defined.

Definition is_univalent_2_bicat_of_groupoidal
           {B : bicat}
           (HB_2 : is_univalent_2 B)
  : is_univalent_2 (bicat_of_groupoidal B).
Proof.
  apply is_univalent_2_fullsubbicat.
  - exact HB_2.
  - exact isaprop_groupoidal.
Defined.

(**
 2. Pseudofunctor from groupoids
 *)
Definition groupoidal_to_inv2cells_data
           (B : bicat)
  : psfunctor_data (bicat_of_groupoidal B) (bicat_of_inv2cells B).
Proof.
  use make_psfunctor_data.
  - exact (λ x, pr1 x ,, tt).
  - exact (λ _ _ f, f).
  - simple refine (λ x y f g α, pr1 α ,, _).
    exact (pr2 y (pr1 x) (pr1 f) (pr1 g) (pr1 α)).
  - refine (λ x, id2 _ ,, _) ; cbn.
    is_iso.
  - refine (λ _ _ _ f g, id2 _ ,, _) ; cbn.
    is_iso.
Defined.

Definition groupoidal_to_inv2cells_laws
           (B : bicat)
  : psfunctor_laws (groupoidal_to_inv2cells_data B).
Proof.
  repeat split ;
    intro ; intros ;
    (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ]) ;
    cbn in *.
  - apply idpath.
  - apply idpath.
  - rewrite id2_rwhisker.
    rewrite !id2_left.
    apply idpath.
  - rewrite lwhisker_id2.
    rewrite !id2_left.
    apply idpath.
  - rewrite id2_rwhisker, lwhisker_id2.
    rewrite !id2_left, !id2_right.
    apply idpath.
  - rewrite id2_left, id2_right.
    apply idpath.
  - rewrite id2_left, id2_right.
    apply idpath.
Qed.

Definition groupoidal_to_inv2cells
           (B : bicat)
  : psfunctor (bicat_of_groupoidal B) (bicat_of_inv2cells B).
Proof.
  use make_psfunctor.
  - exact (groupoidal_to_inv2cells_data B).
  - exact (groupoidal_to_inv2cells_laws B).
  - split ; intros ; apply is_invertible_2cell_bicat_of_inv2cells.
Defined.

(**
 3. Having cores
 *)
Definition has_cores
           (B : bicat)
  : UU
  := ∑ (R : right_universal_arrow
              (groupoidal_to_inv2cells B)),
     ∏ (x : B),
     let ε := pr1 (pr12 R (x ,, tt)) in
     is_eso ε × pseudomonic_1cell ε.
