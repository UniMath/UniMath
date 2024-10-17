Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section IndiscreteTopology.

  Context (C : category).

  Definition indiscrete_topology_selection
    (X : C)
    (S : Sieves.sieve X)
    : hProp
    := make_hProp (is_nat_z_iso (sieve_nat_trans S)) (isaprop_is_nat_z_iso _).

  Lemma indiscrete_topology_maximal_sieve
    : Grothendieck_topology_maximal_sieve_ax indiscrete_topology_selection.
  Proof.
    intros X Y.
    apply (make_is_z_isomorphism _ (identity _)).
    abstract (split; apply id_left).
  Defined.

  Lemma indiscrete_topology_stability
    : Grothendieck_topology_stability_ax indiscrete_topology_selection.
  Proof.
    intros X Y f S HS.
    apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _)).
    apply (Pullback_of_z_iso (g := Subobject_mor S)).
    exact (nat_trafo_z_iso_if_pointwise_z_iso (homset_property _) _ HS).
  Defined.

  Definition indiscrete_topology_transitivity_iso
    {X : C}
    {S : Sieves.sieve X}
    (H : is_nat_z_iso (sieve_nat_trans (PullbackSubobject Pullbacks_PreShv S (# (yoneda C) (identity X)))))
    : z_iso (Subobject_dom S) (yoneda C X).
  Proof.
    refine (z_iso_comp (z_iso_inv _) _).
    - refine (_ ,, Pullback_of_z_iso' _ (Pullbacks_PreShv _ _ _
        (# (yoneda C) (identity X))
        (sieve_nat_trans S))).
      apply functor_on_is_z_isomorphism.
      apply is_z_isomorphism_identity.
    - refine (_ ,, _).
      apply (nat_trafo_z_iso_if_pointwise_z_iso (homset_property _)).
      exact H.
  Defined.

  Lemma indiscrete_topology_transitivity
    : Grothendieck_topology_transitivity_ax indiscrete_topology_selection.
  Proof.
    intros X S H.
    specialize (H X (identity X)).
    apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _)).
    use (is_z_isomorphism_path _ (z_iso_is_z_isomorphism (indiscrete_topology_transitivity_iso H))).
    abstract (
      apply nat_trans_eq_alt;
      intro Y;
      apply funextfun;
      intro x;
      apply id_right
    ).
  Defined.

  Definition indiscrete_is_topology
    : is_Grothendieck_topology indiscrete_topology_selection
    := make_is_Grothendieck_topology
      indiscrete_topology_maximal_sieve
      indiscrete_topology_stability
      indiscrete_topology_transitivity.

  Definition indiscrete_topology
    : Grothendieck_topology C
    := make_Grothendieck_topology
      indiscrete_topology_selection
      indiscrete_is_topology.

End IndiscreteTopology.

Section Sheaves.

  Context {C : category}.
  Context (P : PreShv C).

  Lemma indiscrete_presheaf_is_sheaf
    : is_sheaf (indiscrete_topology C) P.
  Proof.
    intros X S f.
    refine ((_ : is_iso (C := PreShv C) _) _ f).
    apply is_iso_from_is_z_iso.
    apply nat_trafo_z_iso_if_pointwise_z_iso.
    exact (pr2 S).
  Defined.

End Sheaves.
