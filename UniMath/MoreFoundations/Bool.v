(** * Booleans *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Sets.

Definition andb : bool -> bool -> bool.
Proof.
  intros b1 b2; induction b1; [exact b2|exact false].
Defined.

Definition orb : bool -> bool -> bool.
Proof.
  intros b1 b2; induction b1; [exact true|exact b2].
Defined.

Definition implb : bool -> bool -> bool.
Proof.
  intros b1 b2; induction b1; [exact b2|exact true].
Defined.