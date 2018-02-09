
(** The natural numbers *)

Require Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Declare ML Module "nat_syntax_plugin".

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition succ := S.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.

(* note: our mul differs from that in Coq.Init.Nat  *)
Definition mul : nat -> nat -> nat.
Proof.
  intros n m.
  induction n as [|p pm].
  - exact O.
  - exact (pm + m).
Defined.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint max n m :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m :=
  match n, m with
    | O, _ => O
    | S n', O => O
    | S n', S m' => S (min n' m')
  end.

Definition this_is_our_nat := O.
