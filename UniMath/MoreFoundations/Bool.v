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

Lemma andb_is_associative :
  ∏ b1 b2 b3 : bool, andb (andb b1 b2) b3 = andb b1 (andb b2 b3).
Proof.
  intros; induction b1; induction b2; induction b3; reflexivity.
Qed.

Lemma orb_is_associative :
  ∏ b1 b2 b3 : bool, orb (orb b1 b2) b3 = orb b1 (orb b2 b3).
Proof.
  intros; induction b1; induction b2; induction b3; reflexivity.
Qed.

Lemma andb_is_commutative :
  ∏ b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
  intros; induction b1; induction b2; reflexivity.
Qed.

Lemma orb_is_commutative :
  ∏ b1 b2 : bool, orb b1 b2 = orb b2 b1.
Proof.
  intros; induction b1; induction b2; reflexivity.
Qed.