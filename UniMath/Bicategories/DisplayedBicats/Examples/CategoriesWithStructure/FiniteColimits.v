(**
  Bicategories for finite colimits

  We define the bicategory of finitely cocomplete categories and finite colimit preserving functors.
  In particular, we define the bicategories whose objects are categories equipped with colimits for a fixed diagram.

  Contents.
  1. Definition bicategories of categories equipped with
     - an initial object [disp_bicat_initial];
     - binary coproducts [disp_bicat_bincoproducts];
     - and coequalizers respectively [disp_bicat_coequalizers].
  2. Definition bicategory of finite cocomplete categories [disp_bicat_colimits]

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Local Open Scope cat.

(** * 1. Bicategories of categories equipped with a colimit of a fixed diagram *)
Section CategoriesWithChosenInitialAndPreservationUpToIso.

  Definition disp_bicat_initial
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Initial (C : category)).
    - exact (λ C₁ C₂ _ _ F, preserves_initial F).
    - exact (λ C _, identity_preserves_initial _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_initial HF HG).
  Defined.

  Lemma disp_2cells_iscontr_initial
    : disp_2cells_iscontr disp_bicat_initial.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenInitialAndPreservationUpToIso.

Section CategoriesWithChosenBinCoproductsAndPreservationUpToIso.

  Definition disp_bicat_bincoproducts
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, BinCoproducts C).
    - exact (λ C₁ C₂ _ _ F, preserves_bincoproduct F).
    - exact (λ C _, identity_preserves_bincoproduct _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_bincoproduct HF HG).
  Defined.

  Lemma disp_2cells_iscontr_bincoproducts
    : disp_2cells_iscontr disp_bicat_bincoproducts.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenBinCoproductsAndPreservationUpToIso.

Section CategoriesWithChosenCoequalizersAndPreservationUpToIso.

  Definition disp_bicat_coequalizers
    : disp_bicat bicat_of_cats.
  Proof.
    use disp_subbicat.
    - exact (λ C, Coequalizers (C : category)).
    - exact (λ C₁ C₂ _ _ F, preserves_coequalizer F).
    - exact (λ C _, identity_preserves_coequalizer _).
    - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_coequalizer HF HG).
  Defined.

  Lemma disp_2cells_iscontr_coequalizers
    : disp_2cells_iscontr disp_bicat_coequalizers.
  Proof.
    apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenCoequalizersAndPreservationUpToIso.

(** * 2. Bicategory of finitely cocomplete categories *)
Section CategoriesWithChosenFiniteColimitsAndPreservationUpToIso.

  Definition disp_bicat_colimits : disp_bicat bicat_of_cats
    := disp_dirprod_bicat
         disp_bicat_initial
         (disp_dirprod_bicat
            disp_bicat_bincoproducts
            disp_bicat_coequalizers).

  Lemma disp_2cells_iscontr_colimits
    : disp_2cells_iscontr disp_bicat_colimits.
  Proof.
    repeat apply disp_2cells_of_dirprod_iscontr ; apply disp_2cells_iscontr_subbicat.
  Qed.

End CategoriesWithChosenFiniteColimitsAndPreservationUpToIso.
