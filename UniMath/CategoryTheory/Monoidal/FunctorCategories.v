(** some categories of monoidal functors *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Local Open Scope cat.

Section LaxMonoidalFunctorCategory.

Context {C D : category} (M : monoidal C) (N : monoidal D).

Definition disp_cat_lax_monoidal_functors : disp_cat [C,D].
Proof.
  use disp_struct.
  - intro F. exact (fmonoidal_lax M N F).
  - intros F G Fm Gm α. exact (is_mon_nat_trans Fm Gm α).
  - intros; apply isaprop_is_mon_nat_trans.
  - intros F Fm. apply is_mon_nat_trans_identity.
  - intros F G H Fm Gm Hm α β Hα Hβ. exact (is_mon_nat_trans_comp Fm Gm Hm α β Hα Hβ).
Defined.

Definition category_lax_monoidal_functors : category
  := total_category disp_cat_lax_monoidal_functors.

End LaxMonoidalFunctorCategory.

Section SymmetricLaxMonoidalFunctorCategory.

  Context {C D : category} {M : monoidal C} {N : monoidal D} (HM : symmetric M) (HN : symmetric N).

Definition disp_cat_symmetric_lax_monoidal_functors_aux : disp_cat (category_lax_monoidal_functors M N).
Proof.
  use disp_full_sub.
  intro FFm. exact (is_symmetric_monoidal_functor HM HN (pr2 FFm)).
Defined.

Definition disp_cat_symmetric_lax_monoidal_functors : disp_cat [C,D]
  := sigma_disp_cat disp_cat_symmetric_lax_monoidal_functors_aux.

End SymmetricLaxMonoidalFunctorCategory.
