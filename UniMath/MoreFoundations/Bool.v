(** * Booleans *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Sets.

Definition bool_set : hSet := hSetpair _ isasetbool.

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

(* Double check they have the right truth tables: *)
Local Definition andbtt1 : andb true true = true := (idpath _).
Local Definition andbtt2 : andb true false = false := (idpath _).
Local Definition andbtt3 : andb false true = false := (idpath _).
Local Definition andbtt4 : andb false false = false := (idpath _).

Local Definition orbtt1 : orb true true = true := (idpath _).
Local Definition orbtt2 : orb true false = true := (idpath _).
Local Definition orbtt3 : orb false true = true := (idpath _).
Local Definition orbtt4 : orb false false = false := (idpath _).

Local Definition implbtt1 : implb true true = true := (idpath _).
Local Definition implbtt2 : implb true false = false := (idpath _).
Local Definition implbtt3 : implb false true = true := (idpath _).
Local Definition implbtt4 : implb false false = true := (idpath _).