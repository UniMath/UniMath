(** * Example of lists *)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope stn.

(** ** Signature for lists *)

(** Indexes for the sorts. *)
Definition data_sort_idx: ⟦ 2 ⟧ := ●0.
Definition list_sort_idx: ⟦ 2 ⟧ := ●1.

(** Signature with two arities: nil and cons constructors.  *)
Definition list_signature: signature_simple
  := make_signature_simple
      [ (nil ,, list_sort_idx) ;
        ( [data_sort_idx ; list_sort_idx] ,, list_sort_idx )
      ]%list.

Definition data_sort: sorts list_signature := data_sort_idx.
Definition list_sort: sorts list_signature := list_sort_idx.

Definition nil_op: names list_signature := ●0.
Definition cons_op: names list_signature := ●1.

Definition list_algebra (A: hSet) := make_algebra_simple list_signature
  [ A ; listset A ]
  [( λ _, nil ; λ p, cons (pr1 p) (pr12 p) )].

Definition list_nil := build_term_curried nil_op.
Definition list_const := build_term_curried cons_op.
