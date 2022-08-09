(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

Contents :

- tries to identify monoidal dialgebras as inserters in the bicategory of whiskered monoidal categories

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Limits.Inserters.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.


Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalDialgebras.

Require Import UniMath.Bicategories.MonoidalCategories.BicatOfWhiskeredMonCats.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* Import BifunctorNotations. *)

Definition has_inserters_monbicat : has_inserters monbicat.
Proof.
  intros Mon_V Mon_W Fm Gm.
  cbn in Fm, Gm.
  exists (dialgebra (pr1 Fm) (pr1 Gm) ,, dialgebra_monoidal (pr2 Fm) (pr2 Gm)).
  simple refine (_ ,, _ ,, _).
  - cbn. exists (dialgebra_pr1 (pr1 Fm) (pr1 Gm)).
    apply dialgebra_monoidal_pr1.
  - cbn. exists (dialgebra_nat_trans (pr1 Fm) (pr1 Gm)).
    apply dialgebra_monoidal_nat_trans.
  - cbn.
    (* this is crying for a displayed treatment *)
Abort.
