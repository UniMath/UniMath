(**************************************************************************************************

  The category of open subsets

  This file defines the category of open subsets of a topological space, in which the morphisms are
  inclusions. A continuous function between two topological spaces gives a functor in the other
  direction between their categories of opens. These together give an indexed category structure on
  top_cat^op.

  Contents
  1. The category of opens [open_category]
  1.1. It is univalent [is_univalent_open_category]
  2. The functor construction [continuous_to_functor]
  3. The indexed category structure [open_category_indexed]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.PreorderCategories.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
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

(** * 3. The indexed category structure *)

Definition open_category_indexed
  : indexed_cat top_cat^op.
Proof.
  use make_indexed_cat.
  - use make_indexed_cat_data.
    + intro T.
      exact (open_category T ,, is_univalent_open_category T).
    + intros T T'.
      exact continuous_to_functor.
    + intro T.
      exact (nat_trans_id (functor_identity _)).
    + intros T T' T'' F F'.
      exact (nat_trans_id (continuous_to_functor (F · F'))).
  - split.
    + intros T U.
      exists (nat_trans_id (functor_identity _) U).
      abstract easy.
    + intros T T' T'' F F' U.
      exists (nat_trans_id (continuous_to_functor (F · F')) U).
      abstract easy.
  - abstract (
      repeat split;
      intros;
      apply isaprop_subtype_containedIn
    ).
Defined.
