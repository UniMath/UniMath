(** * Notations  *)

Require Export UniMath.MoreFoundations.Foundations.

Delimit Scope type_scope with type.

Reserved Notation "A ⇒ B" (at level 95, no associativity).
(* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with Agda input method *)

Notation "A ⇒ B" := (himpl A B) : logic.

Local Open Scope logic.

Definition hequiv (P Q:hProp) : hProp := (P ⇒ Q) ∧ (Q ⇒ P).

Notation "A ⇔ B" := (hequiv A B) (at level 95, no associativity) : logic.
