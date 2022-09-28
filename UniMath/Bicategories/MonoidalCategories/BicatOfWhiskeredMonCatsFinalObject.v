(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

constructs the final object of the bicategory of whiskered monoidal categories

this resides in a separate file because of the heavy dependencies

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.StandardCategories.

Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.TotalBicategoryLimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Require Import UniMath.Bicategories.MonoidalCategories.BicatOfWhiskeredMonCats.

Local Open Scope cat.

Definition unit_monoidal : monoidal (pr1 unit_category).
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * use make_bifunctor_data.
        -- exact (fun _ _ => tt).
        -- intros. apply idpath.
        -- intros. apply idpath.
      * abstract (repeat split).
    + exists tt.
      repeat split; intro x; induction x; apply isapropunit.
  - abstract (
        do 2 (split; [split; red; intros; [apply isasetunit | split; apply isasetunit] |]);
        split;
        [ do 3 (split; [red; intros; apply isasetunit |]);
          split; apply isasetunit |
          split; red; intros; apply isasetunit]).
Defined.

Definition unit_monoidal_disp_bifinal_obj : disp_bifinal_obj_stronger bidisp_monbicat_disp_bicat (_,,bifinal_cats).
Proof.
  exists unit_monoidal.
  use tpair.
  - intros C M.
    cbn.
    use tpair.
    + use tpair.
      * split; red; intros; apply idpath.
      * abstract (repeat split).
    + split; red; intros; exists (idpath tt); abstract (split; apply isasetunit).
  - intros x xx f g ff gg.
    red; cbn; red; cbn.
    split; intros; apply isasetunit.
Defined.

Definition bifinal_moncats : bifinal_obj monbicat.
Proof.
  use total_bicat_final_stronger.
  - exact monbicat_disp_2cells_isaprop.
  - exact (_,,bifinal_cats).
  - exact unit_monoidal_disp_bifinal_obj.
Defined.
