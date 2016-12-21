(**

This file contains a formalization of lists define as iterated products ([list]).

Written by: Anders Mörtberg, 2016 (inspired by a remark of Vladimir Voevodsky)

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Section preamble.

Definition iterprod (n : nat) (A : UU) : UU.
Proof.
induction n as [|n IHn].
- apply unit.
- apply (A × IHn).
Defined.

End preamble.

(** * Lists over an arbitrary type *)
Section lists.

Context {A : UU}.

(** The type of lists *)
Definition list : UU := Σ n, iterprod n A.

(** The empty list *)
Definition nil : list := (0,,tt).

(** List cons *)
Definition cons (x : A) (xs : list) : list :=
  (S (pr1 xs),, (x,, pr2 xs)).

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Lemma list_ind : Π (P : list -> UU),
     P nil
  -> (Π (x : A) (xs : list), P xs -> P (x :: xs))
  -> Π xs, P xs.
Proof.
intros P Hnil Hcons xs.
induction xs as [n xs].
induction n as [|n IHn].
- induction xs.
  apply Hnil.
- induction xs as [x xs].
  apply (Hcons x (n,,xs) (IHn xs)).
Defined.

Definition foldr {B : UU} (f : A -> B -> B) (b : B) : list -> B :=
  list_ind (fun _ => B) b (fun a _ b' => f a b').

Definition length : list -> nat :=
  foldr (fun _ => S) 0.

(** Variation of foldr that returns a for the empty list and folds the
    rest with the first element as new default value *)
Definition foldr1 (f : A -> A -> A) (a : A) (l : list) : A.
Proof.
destruct l as [[|n] xs].
- apply a.
- induction n as [|n F].
  + apply (pr1 xs).
  + apply (f (pr1 xs) (F (pr2 xs))).
Defined.

End lists.

(** Make the type not implicit for list *)
Arguments list : clear implicits.

Section more_lists.

Definition map {A B : UU} (f : A -> B) : list A -> list B :=
  foldr (λ a l, cons (f a) l) nil.

(** Various unfolding lemmas *)
Lemma foldr_cons {A B : UU} (f : A -> B -> B) (b : B) (x : A) (xs : list A) :
  foldr f b (cons x xs) = f x (foldr f b xs).
Proof.
now destruct xs.
Qed.

Lemma map_nil {A B : UU} (f : A -> B) : map f nil = nil.
Proof.
apply idpath.
Qed.

Lemma map_cons {A B : UU} (f : A -> B) (x : A) (xs : list A) :
  map f (cons x xs) = cons (f x) (map f xs).
Proof.
now destruct xs.
Qed.

Lemma foldr1_cons_nil {A : UU} (f : A -> A -> A) (a : A) (x : A) :
  foldr1 f a (cons x nil) = x.
Proof.
apply idpath.
Qed.

Lemma foldr1_cons {A : UU} (f : A -> A -> A) (a : A) (x y : A) (xs : list A) :
  foldr1 f a (cons x (cons y xs)) = f x (foldr1 f a (cons y xs)).
Proof.
apply idpath.
Qed.

End more_lists.