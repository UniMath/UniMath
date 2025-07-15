(**
  Displayed Bicategories Of Topoi

  In this file, we define bicategories of topoi.

  Contents
  1. Pretopoi [disp_bicat_pretopoi]
  2. Elementary topoi [disp_bicat_elementarytopoi]
  3. Arithmetic topoi [disp_bicat_arithmetic_pretopoi, disp_bicat_elementarytopoi_NNO]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.

Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodExtensivity.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteLimits.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.RegularAndExact.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Extensive.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.SubobjectClassifier.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Exponentials.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.ParameterizedNNO.

Local Open Scope cat.

(** * 1. Pretopoi = Exact & Extensive *)
Section Pretopoi.

  Definition disp_bicat_pretopoi
    : disp_bicat bicat_of_cats.
  Proof.
    apply disp_dirprod_bicat.
    - exact disp_bicat_exact.
    - exact disp_bicat_extensive_cats.
  Defined.

  Lemma disp_bicat_pretopoi_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_pretopoi.
  Proof.
    apply disp_2cells_of_dirprod_iscontr.
    - exact disp_2cells_iscontr_exact.
    - exact disp_2cells_iscontr_extensive_cats.
  Qed.

End Pretopoi.

(** * 2. Elementary Topoi = Finite Limits & Cartesian Closed & Subobject Classifier *)
Section ElementaryTopoi.

  Definition disp_bicat_elementarytopoi'
    : disp_bicat (total_bicat disp_bicat_limits).
  Proof.
    apply disp_dirprod_bicat.
    - exact disp_bicat_exponentials_over_lim.
    - exact disp_bicat_subobject_classifier'.
  Defined.

  Lemma disp_bicat_elementarytopoi'_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_elementarytopoi'.
  Proof.
    apply disp_2cells_of_dirprod_iscontr.
    - apply disp_2cells_iscontr_exponentials_over_lim.
    - apply disp_2cells_iscontr_subobject_classifier'.
  Qed.

  Definition disp_bicat_elementarytopoi
    : disp_bicat bicat_of_cats.
  Proof.
    exact (sigma_bicat _ _ disp_bicat_elementarytopoi').
  Defined.

  Lemma disp_bicat_elementarytopoi_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_elementarytopoi.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_limits.
    - apply disp_bicat_elementarytopoi'_is_locally_contractible.
  Qed.

End ElementaryTopoi.

(** * 3. Arithmetic Topoi *)
Section ArithmeticTopoi.

  Definition disp_bicat_arithmetic_elementarytopoi'
    : disp_bicat (total_bicat disp_bicat_elementarytopoi).
  Proof.
    use disp_subbicat.
    - intros [C [[[T ?] [[P ?] ?]] ?]].
      exact (parameterized_NNO T P).
    - simpl.
      intros C₁ C₂ N₁ N₂ [F [[[? pt] ?] ?]].
      exact (preserves_parameterized_NNO N₁ N₂ _ pt).
    - intro ; intro ; apply id_preserves_parameterized_NNO.
    - exact (λ _ _ _ _ _ _ _ _ p₁ p₂, comp_preserves_parameterized_NNO p₁ p₂).
  Defined.

  Definition disp_bicat_arithmetic_elementarytopoi
    : disp_bicat bicat_of_cats.
  Proof.
    exact (sigma_bicat _ _ disp_bicat_arithmetic_elementarytopoi').
  Defined.

  Definition disp_bicat_arithmetic_pretopoi'
    : disp_bicat (total_bicat disp_bicat_pretopoi).
  Proof.
    use disp_subbicat.
    - simpl.
      intros [C [[[[[T ?] [[P ?] ?]] ?] ?] ?]].
      exact (parameterized_NNO T P).
    - simpl.
      intros C₁ C₂ N₁ N₂ [F [[[[[? pt] ?] ?] ?] ?]].
      exact (preserves_parameterized_NNO N₁ N₂ _ pt).
    - intro ; intro ; apply id_preserves_parameterized_NNO.
    - exact (λ _ _ _ _ _ _ _ _ p₁ p₂, comp_preserves_parameterized_NNO p₁ p₂).
  Defined.

  Definition disp_bicat_arithmetic_pretopoi
    : disp_bicat bicat_of_cats.
  Proof.
    exact (sigma_bicat _ _ disp_bicat_arithmetic_pretopoi').
  Defined.

  Lemma disp_bicat_arithmetic_elementarytopoi'_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_arithmetic_elementarytopoi'.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

  Lemma disp_bicat_arithmetic_elementarytopoi_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_arithmetic_elementarytopoi.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_bicat_elementarytopoi_is_locally_contractible.
    - apply disp_bicat_arithmetic_elementarytopoi'_is_locally_contractible.
  Qed.

  Lemma disp_bicat_arithmetic_pretopoi'_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_arithmetic_pretopoi'.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

  Lemma disp_bicat_arithmetic_pretopoi_is_locally_contractible
    : disp_2cells_iscontr disp_bicat_arithmetic_pretopoi.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_bicat_pretopoi_is_locally_contractible.
    - apply disp_bicat_arithmetic_pretopoi'_is_locally_contractible.
  Qed.

End ArithmeticTopoi.
