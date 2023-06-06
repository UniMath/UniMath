(************************************************************************************

 Bicategories of categories with structure

 In set-theoretical foundations, there is a difference between chosen limits and
 existing limits. In this file, we define bicategories of categories with either
 chosen or existing limits.

 For the remainder of this paragraph, we focus on terminal objects. We have a
 bicategory of categories with chosen limits; the 1-cells are functors that preserve
 the chosen terminal objects up to strict equality. We also have a bicategory of
 categories with limits; the 1-cells are functors that preserve limits (up to iso).
 If we were to look at univalent categories, then these two bicategories coincide.
 Terminal objects are unique up to equality in univalent categories, so if we know
 that a terminal object exists, then we can choose one. In addition, since equality
 corresponds to isomorphism, the two notion of preservation also correspond. If we do
 not require the category to be univalent, then the two aforementioned bicategories
 are actually different.

 In this file, we define these different bicategories. The interest for these
 bicategories come from how the Rezk completion interacts with these notions.

 Note that [disp_bicat_chosen_terminal_obj] is defined as a subbicategory of the
 bicategory of categories, even though terminal objects are in general only unique
 up to equality in univalent categories. We use this construction more as a shortcut
 to obtain the desired definition.

 Contents
 1. Categories with a chosen terminal object
 2. Categories that have a terminal object
 3. Each type of 2-cells in the bicategory of categories with a terminal object (chosen/have) is contractible.

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Local Open Scope cat.

(**
 1. Categories with a chosen terminal object
 *)
Definition disp_bicat_chosen_terminal_obj
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Terminal (pr1 C)).
  - exact (λ C₁ C₂ T₁ T₂ F, preserves_chosen_terminal_eq F T₁ T₂).
  - exact (λ C T, identity_preserves_chosen_terminal_eq T).
  - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_terminal_eq PF PG).
Defined.

Definition cat_with_chosen_terminal_obj
  : bicat
  := total_bicat disp_bicat_chosen_terminal_obj.

(**
 2. Categories that have a terminal object
 *)
Definition disp_bicat_have_terminal_obj
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, @hasTerminal (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_terminal F).
  - exact (λ C _, identity_preserves_terminal _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_terminal HF HG).
Defined.

Definition cat_with_terminal_obj
  : bicat
  := total_bicat disp_bicat_have_terminal_obj.

(* Homotopy levels of each type of 2-cells *)
Lemma disp_2cells_is_contr_have_terminal_obj
  : disp_2cells_iscontr disp_bicat_have_terminal_obj.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_chosen_terminal_obj
  : disp_2cells_iscontr disp_bicat_chosen_terminal_obj.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.
