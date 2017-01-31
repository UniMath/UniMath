(**

This file contains a formalization of lists define as iterated products ([list]).

Written by: Anders Mörtberg, 2016 (inspired by a remark of Vladimir Voevodsky)

*)
Require Import UniMath.Foundations.PartD.

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
Definition list : UU := ∑ n, iterprod n A.

(** The empty list *)
Definition nil : list := (0,,tt).

(** List cons *)
Definition cons (x : A) (xs : list) : list :=
  (S (pr1 xs),, (x,, pr2 xs)).

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Lemma list_ind : ∏ (P : list -> UU),
     P nil
  -> (∏ (x : A) (xs : list), P xs -> P (x :: xs))
  -> ∏ xs, P xs.
Proof.
intros P Hnil Hcons xs.
induction xs as [n xs].
induction n as [|n IHn].
- induction xs.
  apply Hnil.
- simpl in xs.
  induction xs as [x xs].
  apply (Hcons x (n,,xs) (IHn xs)).
Defined.

Lemma list_ind_compute_2
      (P : list -> UU)
      (p0 : P nil)
      (ind : ∏ (x : A) (xs : list), P xs -> P (x :: xs))
      (x : A) (xs : list)
      (f := list_ind P p0 ind) :
  f (x::xs) = ind x xs (f xs).
Proof.
  induction xs as [n s].  (* once we get primitive projections working, we should be able to omit this *)
  reflexivity.
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

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

(** concatenate two lists  *)

Definition concatenate {X} : list X -> list X -> list X
  := λ r s, foldr cons s r.

Lemma concatenateStep {X} (x:X) (r s:list X) :
  concatenate (x::r) s = x :: concatenate r s.
Proof.
  unfold concatenate at 1.
  unfold foldr.
  rewrite list_ind_compute_2.
  reflexivity.
Defined.

(** flatten lists of lists  *)

Definition flatten {X} : list (list X) → list X.
Proof.
  apply list_ind.
  + exact [].
  + intros s _ f. exact (concatenate s f).
Defined.
