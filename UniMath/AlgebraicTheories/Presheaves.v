(**************************************************************************************************

  Presheaves

  Defines what a presheaf for an algebraic theory is and gives constructors, accessors and related
  definitions and lemmas.

  Contents
  1. The definition of a presheaf [presheaf]
  2. The presheaf given by the algebraic theory itself [theory_presheaf]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.
Require Import UniMath.AlgebraicTheories.PresheafCategoryCore.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of a presheaf *)

Definition presheaf_data (T : algebraic_theory) : UU
  := ∑ (P : indexed_set_cat nat), ∏ m n f g, op_ax T P m n f g.

Definition presheaf_data_to_function {T : algebraic_theory} (P : presheaf_data T)
  : nat → hSet
  := pr1 P.

Coercion presheaf_data_to_function : presheaf_data >-> Funclass.

Definition op
  {T : algebraic_theory}
  {P : presheaf_data T}
  {m n : nat}
  (f : P m)
  (g : stn m → T n)
  : op_ax T P m n f g
  := pr2 P m n f g.

Definition make_presheaf_data
  {T : algebraic_theory}
  (P : indexed_set_cat nat)
  (op : ∏ m n f g, op_ax T P m n f g)
  : presheaf_data T
  := P ,, op.

Definition is_presheaf {T : algebraic_theory} (P : presheaf_data T) : UU :=
  (∏ l m n a f g, op_op_ax T P (@op T P) l m n a f g) ×
  (∏ n f, op_pr_ax T P (@op T P) n f).

Definition make_is_presheaf
  {T : algebraic_theory}
  (P : presheaf_data T)
  (op_op : ∏ l m n a f g, op_op_ax T P (@op T P) l m n a f g)
  (op_pr : ∏ n f, op_pr_ax T P (@op T P) n f)
  : is_presheaf P
  := op_op ,, op_pr.

Definition presheaf (T : algebraic_theory) : UU := presheaf_cat T.

#[reversible=no] Coercion presheaf_to_presheaf_data {T : algebraic_theory} (P : presheaf T)
  : presheaf_data T
  := make_presheaf_data (pr1 P) (pr12 P).

Definition make_presheaf
  {T : algebraic_theory}
  (P : presheaf_data T)
  (H : is_presheaf P)
  : presheaf T
  := (pr1 P) ,, (pr2 P) ,, H.

Definition op_op
  {T : algebraic_theory}
  (P : presheaf T)
  {l m n : nat}
  (a : P l)
  (f : stn l → T m)
  (g : stn m → T n)
  : op_op_ax T P (@op T P) l m n a f g
  := pr122 P l m n a f g.

Definition op_pr
  {T : algebraic_theory}
  (P : presheaf T)
  {n : nat}
  (f : P n)
  : op_pr_ax T P (@op T P) n f
  := pr222 P n f.

(** * 2. The presheaf given by the algebraic theory itself *)

Definition theory_presheaf_data
  (T : algebraic_theory)
  : presheaf_data T.
Proof.
  use make_presheaf_data.
  - exact T.
  - intros ? ? f g.
    exact (f • g).
Defined.

Lemma theory_is_presheaf
  (T : algebraic_theory)
  : is_presheaf (theory_presheaf_data T).
Proof.
  use make_is_presheaf.
  - apply comp_comp.
  - apply comp_pr.
Qed.

Definition theory_presheaf
  (T : algebraic_theory)
  : presheaf T
  := make_presheaf _ (theory_is_presheaf T).
