(**

This file contains a formalization of lists define as iterated products ([list]).

Written by: Anders Mörtberg, 2016 (inspired by a remark of Vladimir Voevodsky), Floris van Doorn, december 2017

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
  reflexivity.
Defined.

Definition foldr {B : UU} (f : A -> B -> B) (b : B) : list -> B :=
  list_ind (λ _, B) b (λ a _ b', f a b').

Definition length : list -> nat := pr1.

(** Variation of foldr that returns a for the empty list and folds the
    rest with the first element as new default value *)
Definition foldr1 (f : A -> A -> A) (a : A) : list → A.
Proof.
  apply list_ind.
  - exact a.
  - intros a' l fl. revert l. apply list_ind.
    + exact a'.
    + intros _ _ _. exact (f a' fl).
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
  reflexivity.
Defined.

(** Various unfolding lemmas *)
Lemma foldr_cons {A B : UU} (f : A -> B -> B) (b : B) (x : A) (xs : list A) :
  foldr f b (cons x xs) = f x (foldr f b xs).
Proof.
 reflexivity.
Qed.

Lemma map_nil {A B : UU} (f : A -> B) : map f nil = nil.
Proof.
  apply idpath.
Qed.

Lemma map_cons {A B : UU} (f : A -> B) (x : A) (xs : list A) :
  map f (cons x xs) = cons (f x) (map f xs).
Proof.
  apply idpath.
Qed.

Lemma map_compose {A B C : UU} (f : A → B) (g : B → C) (xs : list A) :
  map (g ∘ f) xs = map g (map f xs).
Proof.
  revert xs. apply list_ind.
  - reflexivity.
  - intros x xs IH. now rewrite !map_cons, IH.
Defined.

Lemma map_idfun {A : UU} (xs : list A) :
  map (idfun A) xs = xs.
Proof.
  revert xs. apply list_ind.
  - reflexivity.
  - intros x xs IH. now rewrite !map_cons, IH.
Defined.

Lemma map_homot {A B : UU} {f g : A → B} (h : f ~ g) (xs : list A) :
  map f xs = map g xs.
Proof.
  revert xs. apply list_ind.
  - reflexivity.
  - intros x xs IH. now rewrite !map_cons, h, IH.
Defined.

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

Local Infix "++" := concatenate.

Lemma concatenateStep {X} (x:X) (r s:list X) :
  (x::r) ++ s = x :: (r ++ s).
Proof.
  reflexivity.
Defined.

Lemma nil_concatenate {X} (r : list X) : nil ++ r = r.
Proof. reflexivity. Defined.

Lemma concatenate_nil {X} (r : list X) : r ++ nil = r.
Proof. revert r. apply list_ind. reflexivity. intros x xs p. exact (maponpaths (cons x) p). Defined.

Lemma assoc_concatenate {X} (r s t : list X) : (r ++ s) ++ t = r ++ (s ++ t).
Proof.
  revert r. apply list_ind.
  - reflexivity.
  - intros x xs p. now rewrite !concatenateStep, p.
Defined.

Lemma map_concatenate {X Y} (f : X → Y) (r s : list X) : map f (r ++ s) = map f r ++ map f s.
Proof.
  revert r. apply list_ind.
  - reflexivity.
  - intros x xs p. now rewrite mapStep, !concatenateStep, mapStep, p.
Defined.

Lemma foldr_concatenate {X Y : UU} (f : X → Y) (l : list X) :
  foldr concatenate [] (map (λ x, f x::[]) l) = map f l.
Proof.
  revert l. apply list_ind.
  - reflexivity.
  - intros x l IH. now rewrite !map_cons, foldr_cons, IH.
Defined.

Lemma foldr1_concatenate {X Y : UU} (f : X → Y) (l : list X) :
  map f l = foldr1 concatenate [] (map (λ x, f x::[]) l).
Proof.
  revert l. apply list_ind.
  - reflexivity.
  - intros x. refine (list_ind _ _ _).
    + reflexivity.
    + intros x' l _ IH. exact (maponpaths (cons (f x)) IH).
Defined.

(** Append a single element to a list *)

Definition append {X} (x : X) (l : list X) : list X :=
  l ++ x::[].

Lemma appendStep {X} (x y : X) (l : list X) : append x (y::l) = y::append x l.
  Proof. reflexivity. Defined.

Lemma append_concatenate {X} (x : X) (l s : list X) : append x (l ++ s) = l ++ append x s.
  Proof. apply assoc_concatenate. Defined.

Lemma map_append {X Y} (f : X → Y) (x : X) (r : list X) : map f (append x r) = append (f x) (map f r).
  Proof. exact (map_concatenate _ _ _). Defined.

(** Reverse a list *)

Definition reverse {X} : list X → list X :=
  foldr append [].

Lemma reverse_nil (X : Type) : reverse (@nil X) = [].
Proof. reflexivity. Defined.

Lemma reverseStep {X} (x : X) (r : list X) : reverse (x::r) = append x (reverse r).
Proof. reflexivity. Defined.

Lemma map_reverse {X Y} (f : X → Y) (r : list X) : map f (reverse r) = reverse (map f r).
Proof.
  revert r. apply list_ind.
  - reflexivity.
  - intros x xs p. now rewrite mapStep, !reverseStep, map_append, p.
Defined.

Lemma reverse_concatenate {X} (l s : list X) : reverse (l ++ s) = reverse s ++ reverse l.
Proof.
  revert l. apply list_ind.
  - symmetry. apply concatenate_nil.
  - intros x xs p. now rewrite concatenateStep, !reverseStep, p, append_concatenate.
Defined.

Lemma reverse_append {X} (x : X) (l : list X) : reverse (append x l) = x :: reverse l.
Proof. unfold append. now rewrite reverse_concatenate, reverseStep, reverse_nil. Defined.

Lemma reverse_reverse {X} (r : list X) : reverse (reverse r) = r.
Proof.
  revert r. apply list_ind.
  - reflexivity.
  - intros x xs p. now rewrite !reverseStep, reverse_append, p.
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
  simple refine (isweq_iso _ (functionToList' _) _ _).
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

Lemma isofhleveliterprod (n : nat) (k : nat) {X : UU} (is1 : isofhlevel n X) : isofhlevel n (iterprod k X).
Proof.
  induction k as [|k IH].
  - apply isofhlevelcontr, iscontrunit.
  - apply isofhleveldirprod.
    + apply is1.
    + apply IH.
Qed.

Lemma isofhlevellist (n : nat) {X : UU} (is1 : isofhlevel (S (S n)) X) : isofhlevel (S (S n)) (list X).
Proof.
  use isofhleveltotal2.
  - intros m k. apply isofhlevelsnprop, isasetnat.
  - intro m. apply isofhleveliterprod, is1.
Qed.