(** * Example of lists *)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope stn.

(** Indexes for the sorts. *)

Definition elem_sort_idx: ⟦ 2 ⟧ := ●0.
Definition list_sort_idx: ⟦ 2 ⟧ := ●1.

(** Signature for lists with two symbols: nil and cons constructors. *)

Definition list_signature: signature_simple
  := make_signature_simple
      [ (nil ,, list_sort_idx) ;
        ( [elem_sort_idx ; list_sort_idx] ,, list_sort_idx )
      ]%list.

(** Names for the constructors. *)

Definition nil_idx: names list_signature := ●0.
Definition cons_idx: names list_signature := ●1.

Definition list_algebra (A: hSet) := make_algebra_simple list_signature
  [ A ; listset A ]
  [( λ _, nil ; λ p, cons (pr1 p) (pr12 p) )].

(** Correspondence between structures and operations in the universal algebra
of lists and standard structures and operations on lists. *)

Lemma elem_sort_id (A: hSet) : supportset (list_algebra A) elem_sort_idx = A.
Proof.
  reflexivity.
Qed.

Lemma list_sort_id (A: hSet) : supportset (list_algebra A) list_sort_idx = listset A.
Proof.
  reflexivity.
Qed.

Definition list_nil (A: hSet) : listset A := ops (list_algebra A) nil_idx tt.

Lemma list_nil_id (A: hSet) : list_nil A = @nil A.
Proof.
  reflexivity.
Qed.

Lemma list_cons_dom_id (A: hSet)
  : dom (list_algebra A) cons_idx = (dirprod A (dirprod (listset A) unit)).
Proof.
  reflexivity.
Qed.

Definition list_cons (A: hSet) : A × listset A × unit → listset A
  := ops (list_algebra A) cons_idx.

Lemma cons_nil_id (A: hSet) (x: A) (l: listset A)
  : list_cons A (x,, (l,, tt)) = cons x l.
Proof.
  reflexivity.
Qed.
