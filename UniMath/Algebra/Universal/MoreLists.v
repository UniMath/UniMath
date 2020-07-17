(** * Additional definitions for lists *)

(**
This file contains list functions and notations which are not directly related to universal algebra.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.

Declare Scope list_scope.

Delimit Scope list_scope with list.

Local Open Scope list_scope.

Bind Scope list_scope with list.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..): list_scope.

Notation "[]" := nil (at level 0, format "[]"): list_scope.

Infix "::" := cons : list_scope.

Lemma length_map {A B: UU} (l: list A) (f: A → B): length (map f l) = length l.
Proof.
  revert l.
  apply list_ind.
  - apply idpath.
  - intros x xs HPind.
    change (map f (x :: xs)) with (cons (f x) (map f xs)).
    change (S (length (map f xs)) = S(length xs)).
    apply maponpaths.
    exact HPind.
Defined.

Definition listset (A: hSet): hSet := make_hSet (list A) (isofhlevellist 0 (setproperty A)).

Definition list_fill {A: UU} (a: A): nat → list A
  := nat_rect (λ _,  list A) nil (λ (n: nat) (l: list A), cons a l).

Lemma map_list_fill {A B: UU} (b: B) (l: list A): map (λ _, b) l = list_fill b (length l).
Proof.
  revert l.
  apply list_ind.
  - apply idpath.
  - intros x xs HPind.
    change (b :: map (λ _: A, b) xs = b :: list_fill b (length xs)).
    apply maponpaths.
    exact HPind.
Defined.

Lemma length_list_fill {A: UU} (a: A) (n: nat): length (list_fill a n) = n.
Proof.
  induction n.
  - apply idpath.
  - change (S (length (list_fill a n)) = S n).
    apply maponpaths.
    exact IHn.
Defined.
