(**************************************************************************************************

  The category of open subsets

  This file defines the category of open subsets of a topological space, in which the morphisms are
  inclusions. A continuous function between two topological spaces gives a functor in the other
  direction between their categories of opens. These together give an indexed category structure on
  top_cat^op.

  Contents
  1. The category of opens [opens_cat_ob]
  1.1. It is univalent [is_univalent_opens_cat_ob]
  2. The functor construction [opens_cat_mor]
  3. The indexed category structure [opens_cat]

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

Section Ob.

  Context (X : TopologicalSpace).

  Definition open_po : po (@Open X) :=
    make_po _ (isporesrel _ _ (subtype_containment_ispreorder X)).

  Definition opens_cat_ob : category := po_category open_po.

(** ** 1.1. It is univalent *)

  Lemma is_univalent_opens_cat_ob
    : is_univalent opens_cat_ob.
  Proof.
    refine (pr2 (po_category_is_univalent_iff_is_antisymm _ _) _).
    - apply isofhlevel_hsubtype.
      apply isasethsubtype.
    - apply isantisymmresrel.
      apply subtype_containment_isantisymm.
  Defined.

End Ob.

(** * 2. The functor construction *)

Definition opens_cat_mor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : opens_cat_ob T' ⟶ opens_cat_ob T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

(** * 3. The indexed category structure *)

Definition opens_cat
  : indexed_cat top_cat^op.
Proof.
  use make_indexed_cat.
  - use make_indexed_cat_data.
    + intro T.
      exact (opens_cat_ob T ,, is_univalent_opens_cat_ob T).
    + intros T T'.
      exact opens_cat_mor.
    + intro T.
      exact (nat_trans_id (functor_identity _)).
    + intros T T' T'' F F'.
      exact (nat_trans_id (opens_cat_mor (F · F'))).
  - split.
    + intros T U.
      exists (nat_trans_id (functor_identity _) U).
      abstract easy.
    + intros T T' T'' F F' U.
      exists (nat_trans_id (opens_cat_mor (F · F')) U).
      abstract easy.
  - abstract (
      repeat split;
      intros;
      apply propproperty
    ).
Defined.
