(***********************************************************************

 Inclusion of univalent categories into categories

 In this file, we define the inclusion pseudofunctor from the bicategory
 of univalent categories to the bicategory of categories. The relevant
 definition is [univ_cats_to_cats].

 ***********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Local Open Scope cat.

Definition univ_cats_to_cats_data
  : psfunctor_data bicat_of_univ_cats bicat_of_cats.
Proof.
  use make_psfunctor_data.
  - exact (λ C, pr1 C).
  - exact (λ _ _ F, F).
  - exact (λ _ _ _ _ n, n).
  - exact (λ _, nat_trans_id _).
  - exact (λ _ _ _ _ _, nat_trans_id _).
Defined.

Definition univ_cats_to_cats_laws
  : psfunctor_laws univ_cats_to_cats_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - exact (!(functor_id _ _)).
  - apply idpath.
  - exact (!(functor_id _ _)).
  - apply idpath.
  - apply idpath.
Qed.

Definition univ_cats_to_cats_invertible_cells
  : invertible_cells univ_cats_to_cats_data.
Proof.
  split.
  - exact (λ C,
           @is_invertible_2cell_id₂ bicat_of_univ_cats C C (functor_identity _)).
  - exact (λ C₁ C₂ C₃ F G,
           @is_invertible_2cell_id₂ bicat_of_univ_cats _ _ (F ∙ G)).
Defined.

Definition univ_cats_to_cats
  : psfunctor bicat_of_univ_cats bicat_of_cats.
Proof.
  use make_psfunctor.
  - exact univ_cats_to_cats_data.
  - exact univ_cats_to_cats_laws.
  - exact univ_cats_to_cats_invertible_cells.
Defined.
