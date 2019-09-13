(* ----------------------------------------------------------------------------------- *)
(** Image of a pseudofunctor                                                           *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Local Open Scope cat.

Definition full_image
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : bicat
  := fullsubbicat B₂ (λ y, ∃ (x : B₁), F x = y).

Definition is_univalent_2_1_full_image
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (B₂_is_univalent_2_1 : is_univalent_2_1 B₂)
  : is_univalent_2_1 (full_image F).
Proof.
  apply is_univalent_2_1_fullsubbicat.
  exact B₂_is_univalent_2_1.
Defined.

Definition is_univalent_2_0_full_image
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (B₂_is_univalent_2 : is_univalent_2 B₂)
  : is_univalent_2_0 (full_image F).
Proof.
  apply is_univalent_2_0_fullsubbicat.
  - exact B₂_is_univalent_2.
  - intro.
    apply isapropishinh.
Defined.

Definition is_univalent_2_full_image
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (B₂_is_univalent_2 : is_univalent_2 B₂)
  : is_univalent_2 (full_image F).
Proof.
  apply is_univalent_2_fullsubbicat.
  - exact B₂_is_univalent_2.
  - intro.
    apply isapropishinh.
Defined.
