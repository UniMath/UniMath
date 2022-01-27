(** **********************************************************

Ralph Matthes

2019, change to [z_iso] as base notion in 2021
*)

(** **********************************************************

Contents :

- build monoidal category for the endofunctors

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
(* Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.HorizontalComposition. *)
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Require Import UniMath.Bicategories.MonoidalCategories.MonoidalFromBicategory.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.


Local Open Scope cat.

Section Endofunctors_as_monoidal_category.

  Context (C : category).

  (*
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]) .

Local Lemma is_nat_trans_left_unitor_data: is_nat_trans (I_pretensor (functorial_composition _ _ _) (functor_identity C)) (functor_identity [C, C]) (@λ_functors C C).
Proof.
  intros F F' m.
  apply nat_trans_eq_alt.
  intro c. cbn.
  rewrite (functor_id F).
  do 2 rewrite id_left.
  apply id_right.
Qed.

Definition left_unitor_of_endofunctors: left_unitor (functorial_composition _ _ _) (functor_identity C).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro F. apply λ_functors.
    * apply is_nat_trans_left_unitor_data.
  + red. intro F. cbn.
    use nat_trafo_z_iso_if_pointwise_z_iso.
    intro c.
    use tpair.
    * exact (identity (pr1 F c)).
    * abstract ( apply Isos.is_inverse_in_precat_identity ).
Defined.

Local Lemma is_nat_trans_right_unitor_data: is_nat_trans (I_posttensor (functorial_composition _ _ _) (functor_identity C))
  (functor_identity [C, C]) (@ρ_functors C C).
Proof.
  intros F F' m.
  apply nat_trans_eq_alt.
  intro c. cbn.
  rewrite id_left.
  rewrite id_right.
  apply id_right.
Qed.

Definition right_unitor_of_endofunctors: right_unitor (functorial_composition _ _ _) (functor_identity C).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro F. apply ρ_functors.
    * apply is_nat_trans_right_unitor_data.
  + red. intro F. cbn.
    use nat_trafo_z_iso_if_pointwise_z_iso.
    intro c.
    use tpair.
    * exact (identity (pr1 F c)).
    * abstract ( apply Isos.is_inverse_in_precat_identity ).
Defined.

Definition associator_of_endofunctors: associator (functorial_composition _ _ _) :=
    associativity_as_nat_z_iso C C C C.

Lemma triangle_eq_of_endofunctors: triangle_eq (functorial_composition _ _ _) (functor_identity C)
  left_unitor_of_endofunctors right_unitor_of_endofunctors associator_of_endofunctors.
Proof.
  intros F G.
  apply nat_trans_eq_alt.
  intro c.
  cbn.
  rewrite functor_id.
  do 3 rewrite id_right.
  apply functor_id.
Qed.

Lemma pentagon_eq_of_endofunctors: pentagon_eq (functorial_composition _ _ _) associator_of_endofunctors.
Proof.
  intros F G H I.
  apply nat_trans_eq_alt.
  intro c.
  cbn.
  do 4 rewrite id_right.
  do 3 rewrite functor_id.
  rewrite id_right.
  apply pathsinv0, functor_id.
Qed.

Definition monoidal_cat_of_endofunctors: monoidal_cat.
Proof.
  use mk_monoidal_cat.
  - exact EndC.
  - apply functorial_composition.
  - apply functor_identity.
  - exact left_unitor_of_endofunctors.
  - exact right_unitor_of_endofunctors.
  - exact associator_of_endofunctors.
  - exact triangle_eq_of_endofunctors.
  - exact pentagon_eq_of_endofunctors.
Defined.
   *)

  Definition monoidal_cat_of_endofunctors: monoidal_cat := monoidal_cat_from_bicat_and_ob(C:=bicat_of_cats) C.
  (** we need this high-level view in order to be able to instantiate [montrafotargetbicat_moncat] in [ActionBasedStrongFunctorsMonoidal] *)

End Endofunctors_as_monoidal_category.
