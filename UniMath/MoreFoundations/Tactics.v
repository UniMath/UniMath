Require Export UniMath.MoreFoundations.Foundations.

(* hSet_induction in Foundations is wrong, so redefine it here: *)

Ltac hSet_induction f e := generalize f; apply hSet_rect; intro e; clear f.
