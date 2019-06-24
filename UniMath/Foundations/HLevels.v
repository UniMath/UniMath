(** * [HLevel(n)] is of hlevel n+1 *)

(**
   Authors: Benedikt Ahrens, Chris Kapulkin
   Title: HLevel(n) is of hlevel n+1
   Date: December 2012
*)

(**
   In this file we prove the main result of this work:
   the type of types of hlevel n is itself of hlevel n+1.
*)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.

(** ** Weak equivalence between identity types in [HLevel] and [U] *)

(** To show that HLevel(n) is of hlevel n + 1, we need to show that
    its path spaces are of hlevel n.

    First, we show that each of its path spaces equivalent to the
     path space of the underlying types.

    More generally, we prove this for any predicate [P : UU -> hProp]
    which we later instantiate with [P := isofhlevel n].
*)

(** Overview of the proof:
   Identity of Sigmas <~> Sigma of Identities <~> Identities in [U] ,
   where the first equivalence is called [weq1] and the second one
   is called [weq2].
*)

Local Lemma weq1  (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (X,, p) = (X',, p' : ∑ (T : UU), P T )
    ≃
    (∑ w : X = X', transportf P w p = p').
Proof.
  apply total2_paths_equiv.
Defined.


(** This helper lemma is needed to show that our fibration
    is indeed a predicate, so that we can instantiate
    the hProposition [P] with this fibration.
*)

Local Lemma ident_is_prop (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X') (w : X = X')
  : isaprop (transportf P w p = p').
Proof.
  apply isapropifcontr.
  apply (pr2 (P X')).
Defined.


(** We construct the equivalence [weq2] as a projection
    from a total space, which, by the previous lemma, is
    a weak equivalence.
*)

Local Lemma weq2 (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (∑ w : X = X', transportf P w p = p')
    ≃
    (X = X').
Proof.
  use weqpr1.
  intro. cbn. apply (pr2 (P X')).
Defined.

(**  Composing [weq1] and [weq2] yields the desired
     weak equivalence.
*)

Local Lemma Id_p_weq_Id (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (X ,, p) = (X',, p' : ∑ T , P T)
    ≃
    X = X'.
Proof.
  set (f := weq1 P X X' p p').
  set (g := weq2 P X X' p p').
  set (fg := weqcomp f g).
  exact fg.
Defined.


(** ** Hlevel of path spaces *)

(**  We show that if [X] and [X'] are of hlevel [n], then so is their
      identity type [X = X'].
*)
(** The proof works differently for [n = 0] and [n = S n'],
    so we treat these two cases in separate lemmas
    [isofhlevel0pathspace] and [isofhlevelSnpathspace] and put them
    together in the lemma [isofhlevelpathspace].
*)

(** *** The case [n = 0] *)

Lemma iscontr_weq (X Y : UU)
  : iscontr X → iscontr Y → iscontr (X ≃ Y).
Proof.
  intros cX cY.
  exists (weqcontrcontr cX cY ).
  intro f.
  apply subtypeEquality.
  { exact isapropisweq. }
  apply funextfun. cbn. intro x. apply (pr2 cY).
Defined.

Lemma isofhlevel0pathspace (X Y : UU)
  : iscontr X -> iscontr Y -> iscontr (X = Y).
Proof.
  intros pX pY.
  set (H := isofhlevelweqb 0 (eqweqmap ,, univalenceAxiom X Y)).
  apply H. clear H.
  apply iscontr_weq;
    assumption.
Defined.


(** *** The case [n = S n'] *)

Lemma isofhlevelSnpathspace : ∏ n : nat, ∏ X Y : UU,
      isofhlevel (S n) Y -> isofhlevel (S n) (X = Y).
Proof.
  intros n X Y pY.
  set (H:=isofhlevelweqb (S n) (eqweqmap ,, univalenceAxiom X Y)).
  apply H.
  apply isofhlevelsnweqtohlevelsn.
  assumption.
Defined.


(** ** The lemma itself *)

Lemma isofhlevelpathspace : ∏ n : nat, ∏ X Y : UU,
      isofhlevel n X -> isofhlevel n Y -> isofhlevel n (X = Y).
Proof.
  intros n.
  induction n as [| n _ ].
  - intros X Y pX pY.
    apply isofhlevel0pathspace;
    assumption.
  - intros.
    apply isofhlevelSnpathspace;
    assumption.
Defined.


(** ** HLevel *)

(** We define the type [HLevel n] of types of hlevel n. *)

Definition HLevel (n : nat) : UU := ∑ X : UU, isofhlevel n X.

(** * Main theorem: [HLevel n] is of hlevel [S n] *)

Lemma isofhlevel_HLevel (n : nat) : isofhlevel (S n) (HLevel n).
Proof.
  cbn.
  intros X X'.
  induction X as [X p].
  induction X' as [X' p'].
  set (H := isofhlevelweqb n
       (Id_p_weq_Id (λ X, (isofhlevel n X,, isapropisofhlevel _ _)) X X' p p')).
  cbn in H.
  apply H.
  apply isofhlevelpathspace;
    assumption.
Defined.

(** ** Aside: Univalence for predicates and hlevels *)

(** As a corollary from [Id_p_weq_Id],
    we obtain a version of the Univalence Axiom for
    predicates on the universe [U].
    In particular, we can instantiate this predicate with
    [isofhlevel n].
*)

Lemma UA_for_Predicates (P : UU -> hProp) (X X' : UU)
     (pX : P X) (pX' : P X') :
  (tpair _ X pX) = (tpair P X' pX') ≃ (X ≃ X').
Proof.
  set (f := Id_p_weq_Id P X X' pX pX').
  set (g := tpair _ _ (univalenceAxiom X X')).
  exact (weqcomp f g).
Defined.

Corollary UA_for_HLevels : ∏ (n : nat) (X X' : HLevel n),
   (X = X') ≃ (pr1 X ≃ pr1 X').
Proof.
  intros n [X pX] [X' pX'].
  simpl.
  apply (UA_for_Predicates
       (λ X, tpair isaprop (isofhlevel n X)
                                      (isapropisofhlevel _ _))).
Defined.
