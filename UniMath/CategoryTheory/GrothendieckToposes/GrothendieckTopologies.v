(** * Definiton of Grothendieck topology
    The following definition is a formalization of the definition in Sheaves in Geometry and Logic,
    Saunders Mac Lane and Ieke Moerdijk, pages 109 and 110.

    Grothendieck topology is a collection J(c) of subobjects of the Yoneda functor, for every object
    of C, such that:
    - The Yoneda functor y(c) is in J(c).
    - Pullback of a subobject in J(c) along any morphism h : c' --> c is in J(c')
    - If S is a subobject of y(c) such that for all objects c' and all morphisms
      h : c' --> c in C the pullback of S along h is in J(c'), then S is in J(c).
  *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.

Local Open Scope logic.
Local Open Scope cat.

Section GrothendieckTopology.

  Context {C : category}.

  Definition sieve_selection : UU := ∏ (c : C), hsubtype (sieve c).

  Definition sieve_selection_to_product (GT : sieve_selection)
    : ∏ (c : C), hsubtype (sieve c)
    := GT.

  Coercion sieve_selection_to_product : sieve_selection >-> Funclass.

  Section IsGrothendieckTopology.

    Context (selection : sieve_selection).

    Definition Grothendieck_topology_maximal_sieve_ax : hProp :=
      ∀ (c : C),
        selection c (Subobjectscategory_ob (identity (yoneda C c)) (identity_isMonic _)).

    Definition Grothendieck_topology_stability_ax : hProp :=
      ∀ (c c' : C) (h : c' --> c) (s : sieve c),
        selection c s ⇒
        selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)).

    Definition Grothendieck_topology_transitivity_ax : hProp :=
      ∀ (c : C) (s : sieve c),
        (∏ (c' : C) (h : c' --> c),
          selection c' (PullbackSubobject Pullbacks_PreShv s (# (yoneda C) h)))
        ⇒ selection c s.

    Definition is_Grothendieck_topology : hProp :=
      Grothendieck_topology_maximal_sieve_ax
      ∧ Grothendieck_topology_stability_ax
      ∧ Grothendieck_topology_transitivity_ax.

    Definition make_is_Grothendieck_topology
      (H1 : Grothendieck_topology_maximal_sieve_ax)
      (H2 : Grothendieck_topology_stability_ax)
      (H3 : Grothendieck_topology_transitivity_ax)
      : is_Grothendieck_topology
      := H1 ,, H2 ,, H3.

  End IsGrothendieckTopology.

  Definition Grothendieck_topology : UU :=
    ∑ selection, is_Grothendieck_topology selection.

  Definition make_Grothendieck_topology
    (selection : sieve_selection)
    (H : is_Grothendieck_topology selection)
    : Grothendieck_topology
    := selection ,, H.

  (** Accessor functions *)
  Coercion Grothendieck_topology_sieve_selection (GT : Grothendieck_topology) :
    sieve_selection := pr1 GT.

  Definition Grothendieck_topology_is_Grothendieck_topology (GT : Grothendieck_topology) :
    is_Grothendieck_topology GT := pr2 GT.

  Definition Grothendieck_topology_maximal_sieve (GT : Grothendieck_topology)
    : Grothendieck_topology_maximal_sieve_ax GT
    := pr1 (Grothendieck_topology_is_Grothendieck_topology GT).

  Definition Grothendieck_topology_stability (GT : Grothendieck_topology)
    : Grothendieck_topology_stability_ax GT
    := pr12 (Grothendieck_topology_is_Grothendieck_topology GT).

  Definition Grothendieck_topology_transitivity (GT : Grothendieck_topology)
    : Grothendieck_topology_transitivity_ax GT
    := pr22 (Grothendieck_topology_is_Grothendieck_topology GT).

End GrothendieckTopology.

Arguments sieve_selection : clear implicits.
Arguments make_is_Grothendieck_topology {C} {selection}.
Arguments make_Grothendieck_topology {C}.
Arguments Grothendieck_topology : clear implicits.
