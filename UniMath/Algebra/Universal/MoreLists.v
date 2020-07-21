(** * Additional definitions, lemmas and notations for lists *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.Maybe.

(** ** Notations for lists *)

Declare Scope list_scope.

Delimit Scope list_scope with list.

Bind Scope list_scope with list.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..): list_scope.

Notation "[]" := nil (at level 0, format "[]"): list_scope.

Infix "::" := cons: list_scope.

Infix "++" := concatenate: list_scope.

Local Open Scope list_scope.

(** *** Proofs that cons is injective on both arguments *)

Definition head {A: UU}: list A → maybe A.
Proof.
  apply list_ind.
  - exact nothing.
  - exact (λ x xs IH, ii1 x).
Defined.

Definition tail {A: UU}: list A → maybe (list A).
Proof.
  apply list_ind.
  - exact nothing.
  - exact (λ x xs IH, ii1 xs).
Defined.

Lemma list_head_cons {A: UU} (x: A) (xs: list A)
  : head (cons x xs) = ii1 x.
Proof.
  apply idpath.
Defined.

Lemma list_tail_cons {A: UU} (x: A) (xs: list A)
  : tail (cons x xs) = ii1 xs.
Proof.
  apply idpath.
Defined.

Theorem cons_inj1 {A: UU} (a1 a2: A) (r1 r2: list A)
  : cons a1 r1 = cons a2 r2 → a1 = a2.
Proof.
  intro H.
  apply (maponpaths head) in H.
  change (just a1 = just a2) in H.
  apply ii1_injectivity in H.
  assumption.
Defined.

Theorem cons_inj2 {A: UU} (a1 a2: A) (r1 r2: list A)
  : cons a1 r1 = cons a2 r2 → r1 = r2.
Proof.
  intro H.
  apply (maponpaths tail) in H.
  change (just r1 = just r2) in H.
  apply ii1_injectivity in H.
  assumption.
Defined.

(** ** Several properties of the length of a list *)

Lemma length_cons {A: UU} (x: A) (xs: list A)
  : length (cons x xs) = S (length xs).
Proof.
  apply idpath.
Defined.

Lemma length_concatenate {A: UU} (l1: list A) (l2: list A)
  : length (concatenate l1 l2) = length l1 + length l2.
Proof.
  revert l1.
  apply list_ind.
  - apply idpath.
  - intros x xs IH.
    change (S (length (concatenate xs l2)) = S (length xs + length l2)).
    apply maponpaths.
    apply IH.
Defined.

Lemma length_sublist1 {A: UU} (l1: list A) (l2: list A)
  : length l1 ≤ length (concatenate l1 l2).
Proof.
  rewrite length_concatenate.
  apply natlehnplusnm.
Defined.

Lemma length_sublist2 {A: UU} (l1: list A) (l2: list A)
  : length l2 ≤ length (concatenate l1 l2).
Proof.
  rewrite length_concatenate.
  rewrite natpluscomm.
  apply natlehnplusnm.
Defined.

Lemma length_map {A B: UU} (l: list A) (f: A → B): length (map f l) = length l.
Proof.
  revert l.
  apply list_ind.
  - apply idpath.
  - intros x xs HPind.
    change (map f (x :: xs)) with (cons (f x) (map f xs)).
    change (S (length (map f xs)) = S(length xs)).
    apply maponpaths.
    exact HPind.
Defined.

(** ** Additional lemmas and definitions *)

Definition listset (A: hSet): hSet := make_hSet (list A) (isofhlevellist 0 (setproperty A)).

Definition fill {A: UU} (a: A): nat → list A
  := nat_rect (λ _,  list A) nil (λ (n: nat) (l: list A), cons a l).

Lemma map_const {A B: UU} (b: B) (l: list A): map (λ _, b) l = fill b (length l).
Proof.
  revert l.
  apply list_ind.
  - apply idpath.
  - intros x xs HPind.
    change (b :: map (λ _: A, b) xs = b :: fill b (length xs)).
    apply maponpaths.
    exact HPind.
Defined.

Lemma length_fill {A: UU} (a: A) (n: nat): length (fill a n) = n.
Proof.
  induction n.
  - apply idpath.
  - change (S (length (fill a n)) = S n).
    apply maponpaths.
    exact IHn.
Defined.

Lemma negpathsconsnil {A: UU} (a: A) (l: list A): cons a l != nil.
Proof.
  intro X.
  apply (maponpaths pr1) in X.
  cbv in X.
  apply negpathssx0 in X.
  assumption.
Defined.

Lemma negpathsnilcons {A: UU} (a: A) (l: list A): nil != cons a l.
Proof.
  intro X.
  apply pathsinv0 in X.
  apply negpathsconsnil in X.
  assumption.
Defined.

(** ** A decidable set is a type where equality is decidable *)

Definition decSet: UU := ∑ (X: UU), isdeceq X.

Definition make_decSet (X : UU) (i : isdeceq X) := X,, i.

Definition pr1decSet: decSet -> UU := pr1.

Coercion pr1decSet: decSet >-> UU.

Definition decproperty (X: decSet) := pr2 X.

(** ** The prefix_remove operation and related properties *)

Definition prefix_remove {A: decSet} (l1 l2: list A): maybe (list A).
Proof.
  revert l1 l2.
  refine (list_ind _ _ _).
  - exact (λ l, just l).
  - intros x xs HP.
    refine (list_ind _ _ _).
    + exact nothing.
    + intros y ys _.
      induction (decproperty A x y).
      * exact (HP ys).
      * exact nothing.
Defined.

Lemma prefix_remove_stepeq {A: decSet} (x: A) (xs1 xs2: list A)
  : prefix_remove (x :: xs1) (x :: xs2) = prefix_remove xs1 xs2.
Proof. 
  unfold prefix_remove.
  cbn.
  induction (decproperty A x x).
  - cbn.
    apply idpath.
  - contradiction (b (idpath x)).
Defined.

Lemma prefix_remove_stepneq {A: decSet} {x1 x2: A} (p: x1 != x2) (xs1 xs2: list A) 
  : prefix_remove (x1 :: xs1) (x2 :: xs2) = nothing.
Proof. 
  unfold prefix_remove.
  cbn.
  induction (decproperty A x1 x2).
  - contradicts a p.
  - apply idpath.
Defined.

Lemma prefix_remove_concatenate {A: decSet} (l1 l2 l3: list A) (tl: list A)
  : prefix_remove l1 l2 = ii1 tl → prefix_remove l1 (l2 ++ l3) = ii1 (tl ++ l3).
Proof.
  revert l1 l2.
  refine (list_ind _ _ _).
  - intros l2 prooftl.
    apply ii1_injectivity in prooftl.
    rewrite prooftl.
    apply idpath.
  - intros x xs HPind.
    refine (list_ind _ _ _).
    + intro HP.
      cbv in HP.
      apply negpathsii2ii1 in HP.
      contradiction.
    + intros x2 x2s HP2.
      rewrite concatenateStep.
      induction (decproperty A x x2) as [xeqx2 | xneqx2].
      * rewrite xeqx2.
        do 2 rewrite prefix_remove_stepeq.
        apply (HPind x2s).
      * rewrite (prefix_remove_stepneq xneqx2).
        intro HP.
        apply negpathsii2ii1 in HP.
        contradiction.
Defined.
