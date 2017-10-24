(** * Notations  *)

Require Export UniMath.MoreFoundations.Foundations.

Reserved Notation "A ⇒ B" (at level 95, no associativity).
(* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with
             Agda input method *)

Notation "A ⇒ B" := (himpl A B) : logic.

Local Open Scope logic.

Definition hequiv (P Q:hProp) : hProp := (P ⇒ Q) ∧ (Q ⇒ P).

Notation "A ⇔ B" := (hequiv A B) (at level 95, no associativity) : logic.

Definition total2_hProp {X : hProp} (Y : X -> hProp) : hProp
  := hProppair (∑ x, Y x) (isaprop_total2 X Y).

Delimit Scope prop with prop.

Notation "'∑' x .. y , P" := (total2_hProp (λ x,.. (total2_hProp (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : prop.
  (* type this in emacs in agda-input method with \sum *)

Notation "'pr11' x" := (pr1 (pr1 x)) (at level 8).
Notation "'pr12' x" := (pr1 (pr2 x)) (at level 8).
Notation "'pr21' x" := (pr2 (pr1 x)) (at level 8).
Notation "'pr22' x" := (pr2 (pr2 x)) (at level 8).

Notation "'pr111' x" := (pr1 (pr1 (pr1 x))) (at level 8).
Notation "'pr112' x" := (pr1 (pr1 (pr2 x))) (at level 8).
Notation "'pr121' x" := (pr1 (pr2 (pr1 x))) (at level 8).
Notation "'pr122' x" := (pr1 (pr2 (pr2 x))) (at level 8).
Notation "'pr211' x" := (pr2 (pr1 (pr1 x))) (at level 8).
Notation "'pr212' x" := (pr2 (pr1 (pr2 x))) (at level 8).
Notation "'pr221' x" := (pr2 (pr2 (pr1 x))) (at level 8).
Notation "'pr222' x" := (pr2 (pr2 (pr2 x))) (at level 8).
