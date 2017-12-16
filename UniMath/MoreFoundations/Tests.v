(** These are tests for the tactics in Tactics.v *)

Add LoadPath "../" as UniMath.
Require Import UniMath.MoreFoundations.Foundations.
Require Import UniMath.MoreFoundations.Tactics.

Goal isaprop unit. hleveltacS. Qed.
Goal isofhlevel 1 unit. hleveltacS. Qed.

Section hlevel_tac_test2.
  Hypothesis (X Y : Type) (xprop : isaprop X) (yprop : isaprop Y).

  Goal isaprop (X × Y). hleveltac. Qed.
  Goal isofhlevel 1 (X × Y). hleveltac. Qed.
  Goal isofhlevel 20 (X × Y). hleveltacS. Qed.
End hlevel_tac_test2.

Section hlevel_tac_test3.
  Hypothesis (n : nat) (X : Type) (Y : X -> UU) (nx : isofhlevel n X).
  Hypothesis Pcontr : ∏ x : X, isofhlevel n (Y x).
  Goal isofhlevel n (total2 Y). hleveltac. Qed.
  Goal isofhlevel (S (S n)) (total2 Y). hleveltacS. Qed.
  Goal isofhlevel (S (S n)) (∑ x : X, Y x). hleveltacS. Qed.
End hlevel_tac_test3.

Section hlevel_tac_test4.
  Hypothesis (n : nat) (X Y : Type) (xlvl : isofhlevel n Y).
  Goal isofhlevel (S n) (X -> Y). hleveltacS. Qed.
End hlevel_tac_test4.

Section hlevel_tac_test5.
  Hypothesis (n : nat) (X Z : Type) (Y : X -> UU)
             (xlvl : forall x, isofhlevel n (Y x)).
  Goal isofhlevel (S n) (forall x : X, Y x). hleveltacS. Qed.
  Goal isofhlevel (S n) (∏ x : X, Y x). hleveltacS. Qed.
End hlevel_tac_test5.

Section hlevel_tac_test6.
  Hypothesis (X : Type) (f : X -> empty) .
  Goal isofhlevel 1 X. hleveltac. Qed.
  Goal isofhlevel 5 X. hleveltacS. Qed.

Section hlevel_tac_test7.
  Variables (n : nat) (X Y : Type) (ncoprod : isofhlevel (S n) (X ⨿ Y)).
  Goal isofhlevel (S n) X. hleveltac. Qed.
  Goal isofhlevel (S (S (S n))) X. hleveltacS. Qed.
  Goal isofhlevel (S n) Y. hleveltac. Qed.
  Goal isofhlevel (S (S (S n))) Y. hleveltacS. Qed.
End hlevel_tac_test7.

Section hlevel_tac_test09.
  Variables (n : nat) (X : Type).
  Goal isofhlevel 1 (isaprop X). hleveltac. Qed.
  Goal isofhlevel 1 (isaset X). hleveltac. Qed.
  Goal isofhlevel 1 (isofhlevel 1 X). hleveltac. Qed.
  Goal isofhlevel 1 (isofhlevel n X). hleveltac. Qed.
End hlevel_tac_test09.
