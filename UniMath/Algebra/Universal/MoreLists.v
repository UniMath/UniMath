(** * Additional definitions for lists *)

(**
This file contains list functions and notations which are not directly related to universal algebra.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.

Definition list_fill {A: UU} (a: A): nat → list A
  := nat_rect (λ _,  list A) nil (λ (n: nat) (l: list A), cons a l).

Definition listset (A: hSet): hSet := make_hSet (list A) (isofhlevellist 0 (setproperty A)).

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Notation "[]" := nil (at level 0, format "[]").

Infix "::" := cons.
