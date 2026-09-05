(** * Tests *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Bool.

(** ** Bool.v *)

(* Double check they have the right truth tables: *)
Goal andb true true = true. Proof. reflexivity. Qed.
Goal andb true false = false. Proof. reflexivity. Qed.
Goal andb false true = false. Proof. reflexivity. Qed.
Goal andb false false = false. Proof. reflexivity. Qed.

Goal orb true true = true. Proof. reflexivity. Qed.
Goal orb true false = true. Proof. reflexivity. Qed.
Goal orb false true = true. Proof. reflexivity. Qed.
Goal orb false false = false. Proof. reflexivity. Qed.

Goal implb true true = true. Proof. reflexivity. Qed.
Goal implb true false = false. Proof. reflexivity. Qed.
Goal implb false true = true. Proof. reflexivity. Qed.
Goal implb false false = true. Proof. reflexivity. Qed.
