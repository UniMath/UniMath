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
Require Import UniMath.Bicategories.Limits.Examples.BicatOfCatsLimits.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.

Definition monbicat_inserter_cone {Mon_V Mon_W : monbicat} (Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧):
  inserter_cone Fm Gm.
Proof.
  cbn in Fm, Gm.
   use make_inserter_cone.
   - exact (dialgebra (pr1 Fm) (pr1 Gm) ,, dialgebra_monoidal (pr2 Fm) (pr2 Gm)).
   - exists (dialgebra_pr1 (pr1 Fm) (pr1 Gm)).
     apply dialgebra_monoidal_pr1.
   - exists (dialgebra_nat_trans (pr1 Fm) (pr1 Gm)).
     apply dialgebra_nat_trans_is_mon_nat_trans.
Defined.

Definition monbicat_inserter_ump_1 {Mon_V Mon_W : monbicat} (Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧):
  has_inserter_ump_1 (monbicat_inserter_cone Fm Gm).
Proof.
  intro q.
  transparent assert (q0 : (inserter_cone (pr1 Fm) (pr1 Gm))).
  { use make_inserter_cone.
    - exact (pr11 q).
    - exact (pr1 (inserter_cone_pr1 q)).
    - exact (pr1 (inserter_cone_cell q)). }
  set (mor_from_q0 := dialgebra_inserter_ump_1 (pr1 Fm) (pr1 Gm) q0).
  use make_inserter_1cell.
  - use tpair.
    + exact mor_from_q0.
    + cbn.
      use tpair.
      * use tpair.
        -- split.
           ++ intros x y.
              use tpair.
              ** cbn. apply (fmonoidal_preservestensordata (pr2 (inserter_cone_pr1 q) :
                                 fmonoidal (pr21 q) (pr2 Mon_V) (pr1 (inserter_cone_pr1 q)))).
              ** cbn. unfold dialgebra_disp_tensor_op, fmonoidal_preservestensordata.
                 (** This is crying even more loudly for a displayed treament. *)
Admitted.

Definition monbicat_inserter_ump_2 {Mon_V Mon_W : monbicat} (Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧):
  has_inserter_ump_2 (monbicat_inserter_cone Fm Gm).
Proof.
Admitted.

Definition monbicat_inserter_ump_eq {Mon_V Mon_W : monbicat} (Fm Gm : monbicat ⟦ Mon_V, Mon_W ⟧):
  has_inserter_ump_eq (monbicat_inserter_cone Fm Gm).
Proof.
Admitted.


Definition has_inserters_monbicat : has_inserters monbicat.
Proof.
  intros Mon_V Mon_W Fm Gm.
  cbn in Fm, Gm.
  exists (dialgebra (pr1 Fm) (pr1 Gm) ,, dialgebra_monoidal (pr2 Fm) (pr2 Gm)).
  simple refine (_ ,, _ ,, _).
  - cbn. exists (dialgebra_pr1 (pr1 Fm) (pr1 Gm)).
    apply dialgebra_monoidal_pr1.
  - cbn. exists (dialgebra_nat_trans (pr1 Fm) (pr1 Gm)).
    apply dialgebra_nat_trans_is_mon_nat_trans.
  - simple refine (_ ,, _ ,, _).
    + exact (monbicat_inserter_ump_1 Fm Gm).
    + exact (monbicat_inserter_ump_2 Fm Gm).
    + exact (monbicat_inserter_ump_eq Fm Gm).
Defined.
