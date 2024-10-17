Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Examples.EmptySieve.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Examples.TerminalSheaf.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section DiscreteTopology.

  Context (C : category).

  Definition discrete_topology_selection
    (c : C)
    : hsubtype (Sieves.sieve c)
    := λ _, htrue.

  Lemma discrete_topology_is_topology
    : is_Grothendieck_topology discrete_topology_selection.
  Proof.
    easy.
  Qed.

  Definition discrete_topology
    : Grothendieck_topology C
    := make_Grothendieck_topology
      discrete_topology_selection
      discrete_topology_is_topology.

End DiscreteTopology.

Section Sheaves.

  Context {C : category}.

  Section Pointwise.

    Context (F : sheaf_cat (discrete_topology C)).
    Context (X : C).

    Let H := pr2 F X
      (make_carrier (discrete_topology C X) (EmptySieve.empty_sieve X) tt)
      (InitialArrow Initial_PreShv _).

    Let FX := (pr1 F : _ ⟶ _) X : hSet.

    Definition discrete_sheaf_value
      : FX
      := yoneda_weq C X (pr1 F) (pr11 H).

    Lemma discrete_sheaf_value_unique
      (x : FX)
      : x = discrete_sheaf_value.
    Proof.
      pose (E := pr2 H (invmap (yoneda_weq C X (pr1 F)) x ,, InitialArrowUnique Initial_PreShv _ _)).
      refine (!eqtohomot (functor_id (pr1 F) X) x @ _).
      exact (eqtohomot (nat_trans_eq_weq (homset_property _) _ _ (base_paths _ _ E) X) (identity X)).
    Qed.

    Definition discrete_sheaf_contractible
      : iscontr FX
      := make_iscontr discrete_sheaf_value discrete_sheaf_value_unique.

    Lemma discrete_sheaf_morphism_irrelevance
      {Y : hSet}
      (f g : Y → FX)
      : f = g.
    Proof.
      apply funextfun.
      intro x.
      apply proofirrelevancecontr.
      apply discrete_sheaf_contractible.
    Qed.

  End Pointwise.

  Definition discrete_topos_to_unit_functor
    : sheaf_cat (discrete_topology C) ⟶ unit_category
    := functor_to_unit _.

  Lemma discrete_topos_to_unit_ff
    : fully_faithful discrete_topos_to_unit_functor.
  Proof.
    intros P Q.
    use isweq_iso.
    - intro f.
      use (_ ,, tt).
      use make_nat_trans.
      + intros X x.
        apply discrete_sheaf_value.
      + abstract (
          intros X Y g;
          apply discrete_sheaf_morphism_irrelevance
        ).
    - abstract (
        intro f;
        apply subtypePath;
        [ intro;
          apply isapropunit
        | apply nat_trans_eq_alt;
          intro X;
          apply discrete_sheaf_morphism_irrelevance ]
      ).
    - abstract (
        intro f;
        apply isasetunit
      ).
  Defined.

  Lemma discrete_topos_to_unit_ses
    : split_essentially_surjective discrete_topos_to_unit_functor.
  Proof.
    intro b.
    exists (terminal_sheaf _).
    apply idtoiso.
    abstract now induction b, (discrete_topos_to_unit_functor (terminal_sheaf _)).
  Defined.

  Definition discrete_topos_is_unit
    : adj_equiv (sheaf_cat (discrete_topology C)) unit_category
    :=
    functor_to_unit _ ,,
      (rad_equivalence_of_cats' _ _ _
        discrete_topos_to_unit_ff
        discrete_topos_to_unit_ses).

End Sheaves.
