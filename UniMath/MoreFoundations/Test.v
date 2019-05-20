(** * Tests *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Bool.

(** ** Bool.v *)

(* Double check they have the right truth tables: *)
Goal andb true true = true. reflexivity. Qed.
Goal andb true false = false. reflexivity. Qed.
Goal andb false true = false. reflexivity. Qed.
Goal andb false false = false. reflexivity. Qed.

Goal orb true true = true. reflexivity. Qed.
Goal orb true false = true. reflexivity. Qed.
Goal orb false true = true. reflexivity. Qed.
Goal orb false false = false. reflexivity. Qed.

Goal implb true true = true. reflexivity. Qed.
Goal implb true false = false. reflexivity. Qed.
Goal implb false true = true. reflexivity. Qed.
Goal implb false false = true. reflexivity. Qed.