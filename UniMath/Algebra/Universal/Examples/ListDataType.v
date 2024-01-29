(** * Example of lists *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.MoreLists.

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

Definition list_algebra (A: UU) : algebra list_signature
  := make_algebra_simple'
       list_signature
       [( A ; list A )]
       [( nil ; cons )].

(** Correspondence between structures and operations in the universal algebra
of lists and standard structures and operations on lists. *)

Lemma elem_sort_id (A: hSet) : support (list_algebra A) elem_sort_idx = A.
Proof.
  reflexivity.
Qed.

Lemma list_sort_id (A: hSet) : support (list_algebra A) list_sort_idx = listset A.
Proof.
  reflexivity.
Qed.

Definition list_nil (A: hSet) : listset A := ops' (list_algebra A) nil_idx.

Lemma list_nil_id : list_nil = @nil.
Proof.
  reflexivity.
Qed.

Lemma list_cons_dom_id (A: hSet)
  : dom (list_algebra A) cons_idx = dirprod A (dirprod (listset A) unit).
Proof.
  reflexivity.
Qed.

Definition list_cons (A: hSet) : A → listset A → listset A
  := ops' (list_algebra A) cons_idx.

Lemma cons_nil_id : list_cons = @cons.
Proof.
  reflexivity.
Qed.
