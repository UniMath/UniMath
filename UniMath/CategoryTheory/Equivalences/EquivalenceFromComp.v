(**************************************************************************************************

  Let F: C → C' be a functor and F' : C' → C'' be a fully faithful functor. Let D be a category with
  colimits. If the precomposition functor (F • F')* : [C'', D] ⟶ [C, D] is an equivalence, then F*
  and F'* are equivalences to.

  Contents
  1. F* is an equivalence [adjoint_equivalence_1_from_comp]
  2. F'* is an equivalence [adjoint_equivalence_2_from_comp]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SurjectivePrecomposition.

Local Open Scope cat.

Section AdjointEquivalenceFromComp.

  Context {C C' C'' : category}.
  Context (F : C ⟶ C').
  Context (F' : C' ⟶ C'').
  Context (HF' : fully_faithful F').

  Context (D : category).
  Context (HD : Colims D).

  Context (Hequiv : adj_equivalence_of_cats (pre_comp_functor (C := D) F' ∙ pre_comp_functor F)).


(** * 1. F* is an equivalence *)

  Definition lan_after_pre_comp_iso
    (P : [C'', D])
    : z_iso (lan_functor HD F' (pre_comp_functor F' P)) P.
  Proof.
    refine (iso_from_fully_faithful_reflection (fully_faithful_from_equivalence _ _ _ Hequiv) _).
    apply (functor_on_z_iso (pre_comp_functor F)).
    exact (z_iso_inv (pre_comp_after_lan_iso _ HF' _ _ _)).
  Defined.

  Definition lan_after_pre_comp_iso_is_counit
    (P : [C'', D])
    : z_iso_mor (lan_after_pre_comp_iso P)
    = counit_from_right_adjoint (is_right_adjoint_precomposition HD F') P.
  Proof.
    apply invmap_eq.
    apply (maponpaths (pre_whisker_in_funcat C C' D F)).
    apply nat_trans_eq_alt.
    intro c.
    apply colim_mor_eq.
    intro v.
    refine (colimArrowCommutes _ _ _ _ @ !_).
    refine (colim_mor_commute _ _ _ _ _ @ !_).
    apply (maponpaths #(P : C'' ⟶ D)).
    apply (homotweqinvweq (weq_from_fully_faithful _ _ _)).
  Defined.

  Definition adjoint_equivalence_1_from_comp
    : adj_equivalence_of_cats (pre_comp_functor (C := D) F').
  Proof.
    use adj_equivalence_from_right_adjoint.
    - apply (is_right_adjoint_precomposition HD).
    - intro P.
      exact (z_iso_is_z_isomorphism (pre_comp_after_lan_iso _ HF' _ HD P)).
    - intro P.
      exact (is_z_isomorphism_path
        (lan_after_pre_comp_iso_is_counit P)
        (z_iso_is_z_isomorphism (lan_after_pre_comp_iso P))).
  Defined.

(** * 2. F'* is an equivalence *)

  Definition adjoint_equivalence_2_from_comp
    : adj_equivalence_of_cats (pre_comp_functor (C := D) F)
    := two_out_of_three_second
    (pre_comp_functor F')
    (pre_comp_functor F)
    (pre_comp_functor F' ∙ pre_comp_functor F)
    (nat_z_iso_id _)
    (adjoint_equivalence_1_from_comp)
    Hequiv.

End AdjointEquivalenceFromComp.
