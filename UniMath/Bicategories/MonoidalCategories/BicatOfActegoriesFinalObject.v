(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

constructs the final object of the bicategory of (elementarily defined) actegories

in a separate file to reduce dependencies of the base file

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.TotalBicategoryLimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.

Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.

Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.

Section A.

  Context {V : category} (Mon_V : monoidal V).

Definition unit_actegory : actegory Mon_V (pr1 unit_category).
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * use make_bifunctor_data.
        -- exact (fun _ _ => tt).
        -- intros. apply idpath.
        -- intros. apply idpath.
      * abstract (repeat split).
    + cbn.
      repeat split; intro x; induction x; apply isapropunit.
  - cbn.
    abstract (split; [| split; [| split]];
    [red; split; red; intros; [apply isasetunit | split; apply isasetunit] |
     red; do 3 (split; [red; intros; apply isasetunit |]); split; apply isasetunit |
     red; intros; apply isasetunit |
     red; intros; apply isasetunit]).
Defined.


Definition unit_actegory_disp_bifinal_obj : disp_bifinal_obj_stronger (bidisp_actbicat_disp_bicat Mon_V) (_,,bifinal_cats).
Proof.
  exists unit_actegory.
  use tpair.
  - intros C ActC.
    cbn.
    use tpair.
    + use tpair.
      * split; red; intros; apply idpath.
      * abstract (repeat split).
    + red; intros; exists (idpath tt); abstract (split; apply isasetunit).
  - intros x xx f g ff gg.
    red; cbn; red; cbn.
    red; intros; apply isasetunit.
Defined.

Definition bifinal_actegories : bifinal_obj (actbicat Mon_V).
Proof.
  use total_bicat_final_stronger.
  - exact (actbicat_disp_2cells_isaprop Mon_V).
  - exact (_,,bifinal_cats).
  - exact unit_actegory_disp_bifinal_obj.
Defined.

End A.
