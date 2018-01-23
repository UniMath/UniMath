(************************************************************************

This file contains various useful tactics

************************************************************************)

Require Import UniMath.MoreFoundations.Foundations.

(** A version of "easy" specialized for the needs of UniMath.
This tactic is supposed to be simple and predictable. The goal
is to use it to finish "trivial" goals *)
Ltac easy :=
  trivial; intros; solve
   [ repeat (solve [trivial | apply pathsinv0; trivial] || split)
   | match goal with | H : ∅ |- _ => induction H end
   | match goal with | H : ¬ _ |- _ => induction H; trivial end
   | match goal with | H : _ → ∅ |- _ => induction H; trivial end
   | match goal with | H : _ → _ → ∅ |- _ => induction H; trivial end ].

(** Override the Coq now tactic so that it uses unimath_easy instead *)
Tactic Notation "now" tactic(t) := t; easy.

(* hSet_induction in Foundations is wrong, so redefine it here: *)
Ltac hSet_induction f e := generalize f; apply hSet_rect; intro e; clear f.

(* When the goal is displayed as x=y and the types of x and y are hard to discern,
   use this tactic -- it will add the type to the context in simplified form. *)
Ltac show_id_type := match goal with |- @paths ?ID _ _ => set (TYPE := ID); simpl in TYPE end.
