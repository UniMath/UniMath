(* -*- coding: utf-8 -*- *)

(** * Lists *)

(** We implement a list of elements of a type X
    as a function from a standard finite finite set to X. *)

Unset Automatic Introduction.
Require Import UniMath.Foundations.StandardFiniteSets.

Definition List X := Σ n, stn n -> X.

Definition nil {X} : List X.
Proof.
  intros.
  exists 0.
  intros [i l].
  induction (nopathsfalsetotrue l).
Defined.

Definition cons {X} (x:X) (s:List X) : List X.
Proof.
  intros ? ? [n f].
  exists (S n).
  intros [i l].
  induction (isdeceqnat i 0).
  { exact x. }
  { refine (f (i-1,,_)).