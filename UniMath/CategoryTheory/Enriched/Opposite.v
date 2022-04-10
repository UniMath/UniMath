Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Enriched.Enriched.

Local Open Scope cat.

Section Opposite.

Context {Mon_V : monoidal_cat}.

Definition opposite_enriched_precat (A : enriched_precat Mon_V) : enriched_precat (swapping_of_monoidal_cat Mon_V).
Proof.
  use make_enriched_precat.
  - use make_enriched_precat_data.
    + exact A.
    + intros x y.
      exact (enriched_cat_mor y x).
    + intro x.
      simpl.
      exact (enriched_cat_id x).
    + intros x y z.
      simpl.
      apply enriched_cat_comp.
  - split; simpl in a, b; simpl.
    + apply (@enriched_id_right _ A).
    + apply (@enriched_id_left _ A).
  - abstract (intros a b c d;
    simpl;
    change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x));
    apply pathsinv0;
    apply z_iso_inv_on_right;
    apply (@enriched_assoc _ A)).
Defined.

Definition opposite_enriched_functor {A B : enriched_precat Mon_V} (F : enriched_functor A B) : enriched_functor (opposite_enriched_precat A) (opposite_enriched_precat B).
Proof.
  use make_enriched_functor.
  - use make_enriched_functor_data.
    + intro x.
      exact (F x).
    + intros x y.
      exact (enriched_functor_on_morphisms F y x).
  - intro x.
    cbn.
    apply enriched_functor_on_identity.
  - intros x y z.
    cbn.
    apply enriched_functor_on_comp.
Defined.

(* note the direction *)
Definition opposite_enriched_nat_trans {A B : enriched_precat Mon_V} {F G : enriched_functor A B} (a : enriched_nat_trans F G) : enriched_nat_trans (opposite_enriched_functor G) (opposite_enriched_functor F).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (a x).
  - intros x y.
    cbn.
    apply pathsinv0.
    apply (enriched_nat_trans_ax a).
Defined.

End Opposite.
