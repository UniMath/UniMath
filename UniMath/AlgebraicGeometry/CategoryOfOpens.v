(**************************************************************************************************

  The category of open subsets

  This file defines the category of open subsets of a topological space, in which the morphisms are
  inclusions. A continuous function between two topological spaces gives a functor in the other
  direction between their categories of opens. This file defines this functor and shows that for the
  identity function or the composition of two continuous functions, the result of this construction
  is respectively isomorphic to the identity functor or the compositions of the individual functors.

  Contents
  1. The category of opens [open_category]
  1.1. It is univalent [is_univalent_open_category]
  2. The functor construction [continuous_to_functor]
  2.1. When applied to the identity function [continuous_to_functor_identity]
  2.2. When applied to the composition of two continuous functions [continuous_to_functor_compose]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.PreorderCategories.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.

Local Open Scope cat.

(** * 1. The category of opens *)

Section open_category.

  Context (X : TopologicalSpace).

  Definition open_po : po (@Open X) :=
    make_po _ (isporesrel _ _ (subtype_containment_ispreorder X)).

  Definition open_category : category := po_category open_po.

(** ** 1.1. It is univalent *)

  Lemma is_univalent_open_category
    : is_univalent open_category.
  Proof.
    refine (pr2 (po_category_is_univalent_iff_is_antisymm _ _) _).
    - apply isofhlevel_hsubtype.
      apply isasethsubtype.
    - apply isantisymmresrel.
      apply subtype_containment_isantisymm.
  Defined.

End open_category.

(** * 2. The functor construction *)

Definition continuous_to_functor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : open_category T' ⟶ open_category T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

(** ** 2.1. When applied to the identity function *)

Definition continuous_to_functor_identity
  (T : TopologicalSpace)
  : z_iso (C := [_, _]) (continuous_to_functor (identity (C := top_cat) T)) (functor_identity _).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (functor_identity _)).
  - exact (nat_trans_id (functor_identity _)).
  - abstract (
      split;
      apply nat_trans_eq_alt;
      intro;
      easy
    ).
Defined.

(** ** 2.2. When applied to the composition of two continuous functions *)

Definition continuous_to_functor_compose
  {T T' T'' : TopologicalSpace}
  (F : top_cat⟦T, T'⟧)
  (F' : top_cat⟦T', T''⟧)
  : z_iso (C := [_, _])
    (continuous_to_functor (F · F'))
    (continuous_to_functor F' ∙ continuous_to_functor F).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - abstract (
      split;
      apply nat_trans_eq_alt;
      intro;
      easy
    ).
Defined.
