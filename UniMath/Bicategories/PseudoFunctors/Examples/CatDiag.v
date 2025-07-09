(*******************************************************************************

 The diagonal pseudofunctor on univalent categories

 In this file, we define the diagonal pseudofunctor on the bicategory of
 univalent categories. It sends every category `C` to `C × C`.

 *******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Definition diag_univ_cat_data
  : psfunctor_data bicat_of_univ_cats bicat_of_univ_cats.
Proof.
  use make_psfunctor_data.
  - exact (λ C, univalent_category_binproduct C C).
  - exact (λ C D F, pair_functor F F).
  - exact (λ C₁ C₂ F G τ, pair_nat_trans τ τ).
  - exact (λ C, nat_trans_id _).
  - exact (λ C₁ C₂ C₃ F G, nat_trans_id _).
Defined.

Proposition diag_univ_cat_laws
  : psfunctor_laws diag_univ_cat_data.
Proof.
  repeat split ;
  intro ;
  intros ;
  (use nat_trans_eq ; [ apply homset_property | ]) ;
  intro ;
  use pathsdirprod ;
  cbn ;
  try (apply idpath) ;
  rewrite ?id_left, ?id_right ;
  try (apply idpath) ;
  refine (!_) ;
  apply functor_id.
Qed.

Definition diag_univ_cat_invertibles
  : invertible_cells diag_univ_cat_data.
Proof.
  split.
  - intro C ; cbn.
    use is_nat_z_iso_to_is_invertible_2cell.
    exact (pr2 (nat_z_iso_id _)).
  - intros C₁ C₂ C₃ F G ; cbn.
    use is_nat_z_iso_to_is_invertible_2cell.
    exact (pr2 (nat_z_iso_id _)).
Defined.

Definition diag_univ_cat
  : psfunctor bicat_of_univ_cats bicat_of_univ_cats.
Proof.
  use make_psfunctor.
  - exact diag_univ_cat_data.
  - exact diag_univ_cat_laws.
  - exact diag_univ_cat_invertibles.
Defined.
