(**

This file contains a formalization of lists define as iterated products ([list]).

Written by: Anders Mörtberg, 2016 (inspired by a remark of Vladimir Voevodsky)

*)

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.

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
  list_ind (λ _, B) b (λ a _ b', f a b').

Definition length : list -> nat := pr1.

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

(** The n-th element of a list *)

Fixpoint nth'' n i : i < n -> iterprod n A -> A
  (* eventually figure out how to use "induction" alone to define this *)
  := match n, i with
     |   0,   _ => λ r x, fromempty (nopathsfalsetotrue r)
     | S n,   0 => λ r x, pr1 x
     | S n, S i => λ r x, nth'' n i r (pr2 x)
     end.

Definition nth' n : iterprod n A -> stn n -> A.
Proof.
  intros x i.
  exact (nth'' n (pr1 i) (pr2 i) x).
Defined.

Lemma nth'_step n (x:iterprod (S n) A) i (I:i<n) :
  nth' (S n) x (stnpair (S n) (S i) I) = nth' n (pr2 x) (stnpair n i I).
Proof.
  reflexivity.
Defined.

Definition nth x : stn(length x) -> A.
Proof.
  intros i. exact (nth' (length x) (pr2 x) i).
Defined.

Definition functionToList' n : (stn n -> A) -> iterprod n A.
Proof.
  intros f.
  induction n as [|n I].
  - exact tt.
  - exists (f (●0))%stn.
    exact (I(f ∘ dni (●0)))%stn.
Defined.

Definition functionToList n : (stn n -> A) -> list.
Proof.
  intros f.
  exact (n ,, functionToList' n f).
Defined.

Section Test.

  Local Open Scope stn.

  Context {a b c d:A}.
  Let x := a::b::c::d::[].
  Goal nth x (●0) = a. reflexivity. Qed.
  Goal nth x (●1) = b. reflexivity. Qed.
  Goal nth x (●2) = c. reflexivity. Qed.
  Goal nth x (●3) = d. reflexivity. Qed.

  Goal functionToList _ (nth x) = x. reflexivity. Qed.

End Test.

End lists.

(** Make the type not implicit for list *)
Arguments list : clear implicits.

Section more_lists.

Definition map {A B : UU} (f : A -> B) : list A -> list B :=
  foldr (λ a l, cons (f a) l) nil.

Lemma mapStep {A B : UU} (f : A -> B) (a:A) (x:list A) : map f (cons a x) = cons (f a) (map f x).
Proof.
  induction x as [n x].
  reflexivity.
Defined.

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

Lemma flattenStep {X} (x:list X) (m : list(list X)) : flatten (x::m) = concatenate x (flatten m).
Proof.
  unfold flatten.
  rewrite list_ind_compute_2.
  reflexivity.
Defined.

(** between ≃ lists and functions  *)

Lemma isweqlistfun {A} n : isweq (@nth' A n).
Proof.
  simple refine (gradth _ (functionToList' _) _ _).
  - intros. induction n as [|n N].
    + apply isapropunit.
    + simpl in x. induction x as [a x]. apply dirprodeq.
      * simpl. reflexivity.
      * simpl. apply N.
  - intros. apply funextfun; intro i.
    induction n as [|n N].
    + apply fromempty. now apply negstn0.
    + induction i as [i I].
      induction i as [|i IHi].
      * unfold nth', functionToList'; simpl. apply maponpaths. now apply subtypeEquality_prop.
      * change (hProptoType (i<n)) in I.
        exact (nth'_step _ (functionToList' _ _) _ _ @ N _ _).
Defined.

Corollary weqlistfun {A} n : (iterprod n A) ≃ (stn n -> A).
Proof.
  exact (weqpair _ (isweqlistfun _)).
Defined.
