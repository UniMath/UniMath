(** **********************************************************

Ralph Matthes

2019
*)

(** **********************************************************

Contents :

- build monoidal category for the endofunctors

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Section Endofunctors_as_monoidal_category.

  Context {C : category}.
  Variable hs : has_homsets C.

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .

Definition monoidal_precat_of_endofunctors: monoidal_precat.
Proof.
  use mk_monoidal_precat.
  - exact EndC.
  - apply functorial_composition.
  - apply functor_identity.
  - red. use mk_nat_iso.
    + use mk_nat_trans.
      * intro F. apply λ_functor.
      * intros F F' m.
        apply nat_trans_eq; try assumption.
        intro c. cbn.
        rewrite functor_id.
        rewrite id_left.
        do 2 rewrite id_right.
        apply idpath.
    + red. intro F.
      use functor_iso_if_pointwise_iso.
      intro c.
      apply Isos.is_iso_from_is_z_iso.
      use tpair.
      * exact (identity (pr1 F c)).
      * cbn.
        apply Isos.is_inverse_in_precat_identity.
  - red. use mk_nat_iso.
    + use mk_nat_trans.
      * intro F. apply ρ_functor.
      * intros F F' m.
        apply nat_trans_eq; try assumption.
        intro c. cbn.
        rewrite id_left.
        rewrite id_right.
        apply idpath.
    + red. intro F.
      use functor_iso_if_pointwise_iso.
      intro c.
      apply Isos.is_iso_from_is_z_iso.
      use tpair.
      * exact (identity (pr1 F c)).
      * cbn.
        apply Isos.is_inverse_in_precat_identity.
  - red.
    use mk_nat_iso.
    + use mk_nat_trans.
      * intro F. apply α_functor.
      * intros F F' m.
        apply nat_trans_eq; try assumption.
        intro c. cbn.
        rewrite id_left.
        rewrite id_right.
        rewrite <- assoc.
        apply maponpaths.
        eapply pathscomp0.
        { apply functor_comp. }
        apply idpath.
    + intro F; use functor_iso_if_pointwise_iso; intro c; apply Isos.is_iso_from_is_z_iso.
      use tpair.
      * apply α_functor_inv.
      * cbn.
        apply Isos.is_inverse_in_precat_identity.
  - red; cbn.
    intros F G.
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    do 3 rewrite id_left.
    apply idpath.
  - red; cbn.
    intros F G H I.
    apply nat_trans_eq; try assumption.
    intro c.
    cbn.
    do 4 rewrite functor_id.
    do 5 rewrite id_left.
    apply idpath.
Defined.

(* an alternative definition should instantiate the bicategory of categories with the given category [C] by means of [monoidal_precat_from_prebicat_and_ob] in [BicategoryFromMonoidal]. *)

End Endofunctors_as_monoidal_category.
