(** * Additional definitions, lemmas and notations for lists. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Export UniMath.Combinatorics.Lists.

Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.DecSet.

(** ** Notations for lists *)

Declare Scope list_scope.

Delimit Scope list_scope with list.

Bind Scope list_scope with list.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..): list_scope.

Notation "[]" := nil (at level 0, format "[]"): list_scope.

Infix "::" := cons: list_scope.

Infix "++" := concatenate: list_scope.

Local Open Scope list_scope.

(** *** Proofs that [cons] is injective on both arguments *)

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

(** ** Several properties for the length of a list *)

Lemma length_cons {A: UU} (x: A) (xs: list A)
  : length (cons x xs) = S (length xs).
Proof.
  apply idpath.
Defined.

Lemma length_zero_back {A: UU} (l: list A): length l = 0 → l = [].
Proof.
  revert l.
  refine (list_ind _ _ _).
  - reflexivity.
  - intros x xs _ HP.
    rewrite length_cons in HP.
    apply negpathssx0 in HP.
    contradiction.
Defined.

Lemma length_one_back {A: UU} (l: list A) (l1: length l = 1): ∑ x: A, l = [x].
Proof.
  induction l.
  cbn in l1.
  induction (! l1).
  induction pr2 as [x xs].
  exists x.
  induction xs.
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

Definition fill {A: UU} (a: A): nat → list A := λ n, n ,, vector_fill a n.

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
  apply idpath.
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

(** ** The [prefix_remove] operation and related properties. 

If [l2] is a prefix of [l1], then [prefix_remove l1 l2] returns [just l] where [l] is the only list such
that [l2 ++ l = l1]. Otherwise [prefix_remove l1 l2] returns [nothing]. It is required for [l1] and [l2]
to be of type [list A] with [A: decSet].
*)

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

Lemma prefix_remove_stepback {A: decSet} (x1 x2: A) (xs1 xs2: list A)
  : prefix_remove (x1 :: xs1) (x2 :: xs2) != nothing → x1 = x2.
Proof.
  induction (decproperty A x1 x2) as [x1eqx2 | x1neqx2] ; intro HP.
  - assumption.
  - rewrite (prefix_remove_stepneq x1neqx2) in HP.
    apply fromempty.
    apply (HP (idpath _)).
Defined.

Definition prefix_remove_back {A: decSet} (l1 l2 l3: list A):
  prefix_remove l1 l2 = just l3 → l2 = l1 ++ l3.
Proof. 
  revert l1 l2.
  refine (list_ind _ _ _).
  - intros l2 prefixnil.
    cbn in prefixnil.
    apply just_injectivity in prefixnil.
    cbn.
    assumption.
  - intros x1 xs1 HPind.
    refine (list_ind _ _ _).
    + intro prefixxs.
      cbn in prefixxs.
      apply negpathsii2ii1 in prefixxs.
      contradiction.
    + intros x2 xs2 HP2ind HP.
      induction (decproperty A x1 x2) as [x1eqx2 | x1neqx2].
      * rewrite x1eqx2 in *.
        rewrite prefix_remove_stepeq in HP.
        rewrite concatenateStep.
        rewrite (HPind xs2 HP).
        apply idpath.
      * rewrite (prefix_remove_stepneq x1neqx2) in HP.
        contradiction (negpathsii2ii1 _ _ HP).
Defined.

Lemma prefix_remove_self {A: decSet} (l: list A): prefix_remove l l = just [].
Proof.
  revert l.
  apply list_ind.
  - apply idpath.
  - intros x xs IH.
    rewrite prefix_remove_stepeq.
    apply IH.
Defined. 

Definition isprefix {A: decSet} (l1 l2: list A): UU := prefix_remove l1 l2 != nothing.

Lemma isprefix_self {A: decSet} (l: list A): isprefix l l.
Proof. 
  unfold isprefix.
  rewrite prefix_remove_self.
  apply negpathsii1ii2.
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

Lemma prefix_remove_concatenate2 {A: decSet} (l1 l2 l3: list A)
  : length l1 ≤ length l2 → prefix_remove l1 l2 = nothing → prefix_remove l1 (l2 ++ l3) = nothing.
Proof.
  revert l1 l2.
  refine (list_ind _ _ _).
  - intros l2 Hlen Hpref.
    contradiction (negpathsii1ii2 _ _ Hpref).
  - intros x1 xs1 IH.
    refine (list_ind _ _ _).
    + intros Hlen Hpref.
      contradiction (negnatlehsn0 _ Hlen).
    + intros x2 xs2 _ Hlen Hpref.
      rewrite concatenateStep.
      induction (decproperty A x1 x2) as [x1eqx2 | x1neqx2].
      * induction x1eqx2.
        rewrite prefix_remove_stepeq.
        rewrite prefix_remove_stepeq in Hpref.
        apply (IH xs2 Hlen Hpref).
      * apply (prefix_remove_stepneq x1neqx2).
Defined.

Lemma prefix_remove_prefix {A: decSet} (l1 l2: list A): prefix_remove l1 (l1 ++ l2) = just l2.
Proof.
  revert l1.
  refine (list_ind _ _ _).
  - reflexivity.
  - intros x xs IHl1.
    rewrite concatenateStep.
    rewrite prefix_remove_stepeq.
    assumption.
Defined.

(** ** The [drop] operation and related properties. 

If [l] is a list and [n] a natural number, [drop l n] returns the list obtained from l after removing
the first n elements. If n > length l, then [drop l n = nil].
*)

Definition drop {A: UU} (l: list A) (n: nat): list A.
Proof.
  revert l.
  induction n.
  - exact (idfun _).
  - apply list_ind.
    + exact nil.
    + intros x xs _.
      exact (IHn xs).
Defined.

Lemma drop_nil {A: UU} {n: nat}: @drop A [] n = [].
Proof.
  induction n ; apply idpath.
Defined.

Lemma drop_zero {A: UU} (l: list A): drop l 0 = l.
Proof.
  revert l.
  apply list_ind; trivial.
Defined.

Lemma drop_step {A: UU} (x: A) (xs: list A) (n: nat)
  : drop (x :: xs) (S n) = drop xs n.
Proof.
  apply idpath.
Defined.

Lemma drop_full {A: UU} (l: list A): drop l (length l) = nil.
Proof.
  revert l; apply list_ind ; trivial.
Defined.

Lemma drop_concatenate {A: UU} (l1 l2: list A) (n: nat) (nok: n ≤ length l1): drop (l1 ++ l2) n = (drop l1 n) ++ l2.
Proof.
  revert l1 nok.
  induction n.
  - reflexivity.
  - refine (list_ind _ _ _).
    + intros.
      contradiction (negnatlehsn0 _ nok).
    + intros x xs _ sok.
      rewrite concatenateStep.
      do 2rewrite drop_step.
      apply (IHn xs sok).
Defined.

Lemma prefix_remove_drop {A: decSet} (l1 l2: list A)
  : prefix_remove l1 l2 != nothing → prefix_remove l1 l2 = just (drop l2 (length l1)).
Proof.
  revert l1 l2.
  refine (list_ind _ _ _).
  - reflexivity.
  - intros x1 xs1 IH.
    refine (list_ind _ _ _).
    + contradiction.
    + intros x2 xs2 _ prefixok.
      induction (decproperty A x1 x2) as [x1eqx2 | x1neqx2].
      * induction x1eqx2.
        rewrite prefix_remove_stepeq.
        rewrite prefix_remove_stepeq in prefixok.
        apply (IH xs2 prefixok).
      * rewrite (prefix_remove_stepneq x1neqx2) in prefixok.
        contradiction prefixok.
        apply idpath.
Defined.

Lemma length_drop {A: decSet} (l: list A) (n: nat): length (drop l n) = length l - n.
Proof.
  revert l n.
  refine (list_ind _ _ _).
  - intro n.
    rewrite drop_nil.
    induction n.
    + apply idpath.
    + change (0 = 0 - (1+ n)).
      rewrite <- natminusminus.
      assumption.
  - intros x xs IH.
    induction n.
    + apply idpath.
    + rewrite drop_step.
      rewrite length_cons.
      apply (IH n).
Defined.
