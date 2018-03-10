(** * Logical equivalence for propositions *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.LogicalEquivalence.Types.
Require Export UniMath.MoreFoundations.Notations.

Local Open Scope logic.

(** ** Contents

- Conjunction
- Disjunction
*)

(** Two propositions are equal just when they're bi-implicative. *)
Definition weqlogeq (P Q : hProp) : (P = Q) ≃ (P ⇔ Q).
Proof.
  apply weqimplimpl.
  - intro e. induction e. apply isrefl_logeq.
  - intro c. apply hPropUnivalence.
    + exact (pr1 c).
    + exact (pr2 c).
  - apply isasethProp.
  - apply propproperty.
Defined.

(** Two propositions are logically equivalent just when they're equivalent. *)
Definition weq_logeq_weq (P Q : hProp) : (pr1 P <-> pr1 Q) ≃ (P ≃ Q).
Proof.
  use weq_iso.
  - intros logeqPQ; apply logeqweq; intros x; apply logeqPQ; exact x.
  - intros weqPQ.
    use dirprodpair.
    + apply weqPQ.
    + apply invmap, weqPQ.
  - intros logeq; cbn.
    apply pathsdirprod.
    + reflexivity.
    + apply funextfun; intros ?.
      apply proofirrelevance, propproperty.
  - intros weqPQ.
    apply subtypeEquality'.
    + reflexivity.
    + apply isapropisweq.
Defined.

(** One might further want the following weak equivalence, which states that
    two propositions are logically equivalent just when they're bi-implicative:
    <<
      Definition weq_logeq_hequiv (P Q : hProp) : (pr1 P <-> pr1 Q) ≃ (P ⇔ Q).
    >>
    However, it has a trivial proof: `apply idweq`.
 *)

(** Two propositions are bi-implicative just when their underlying types are. *)

Lemma hequiv_if_both_true (P Q : hProp) : P -> Q -> ( P ⇔ Q ).
Proof.
  intros p q.
  split.
  - intros _. exact q.
  - intros _. exact p.
Defined.

Lemma hequiv_if_both_false (P Q : hProp) : ¬P -> ¬Q -> ( P ⇔ Q ).
Proof.
  intros np nq.
  split.
  - intros p. apply fromempty. exact (np p).
  - intros q. apply fromempty. exact (nq q).
Defined.

(** ** Conjunction *)

(* This is already in Foundations/Propositions.v *)
(* Lemma islogeqcommhdisj {P Q : hProp} : hdisj P Q <-> hdisj Q P. *)

Lemma hequiv_assoc_conj {P Q R : hProp} : (P ∧ Q) ∧ R ⇔ P ∧ (Q ∧ R).
Proof.
  apply logeq_assoc_dirprod.
Defined.

Lemma hequiv_comm_conj {P Q : hProp} : P ∧ Q ⇔ Q ∧ P.
Proof.
  apply logeq_comm_dirprod.
Defined.

(** Projections from conjuction with [htrue] *)
Lemma hequiv_conj_true {P : hProp} : htrue ∧ P ⇔ P.
Proof.
  apply logeq_dirprod_unit_l.
Defined.

(** ** Disjunction *)

Lemma logeq_assoc_disj {P Q R : hProp} : (P ∨ Q) ∨ R <-> P ∨ (Q ∨ R).
Proof.
  split.
  - apply hinhuniv; intros hPQR.
    induction hPQR as [hPQ|hR].
    + use (hinhuniv _ hPQ); clear hPQ; intros hPQ.
      induction hPQ as [hP|hQ].
      * exact (hinhpr (ii1 hP)).
      * exact (hinhpr (ii2 (hinhpr (ii1 hQ)))).
    + exact (hinhpr (ii2 (hinhpr (ii2 hR)))).
  - apply hinhuniv; intros hPQR.
    induction hPQR as [hP|hQR].
    + exact (hinhpr (ii1 (hinhpr (ii1 hP)))).
    + use (hinhuniv _ hQR); clear hQR; intros hQR.
      induction hQR as [hQ|hR].
      * exact (hinhpr (ii1 (hinhpr (ii2 hQ)))).
      * exact (hinhpr (ii2 hR)).
Defined.

Lemma logeq_conj_with_disj {P Q : hProp} : P ∧ (P ∨ Q) <-> P.
Proof.
  split.
  - intros hPPQ; apply (pr1 hPPQ).
  - intros hP.
    split; [ apply hP | apply (hinhpr (ii1 hP)) ].
Defined.

Lemma logeq_disj_with_conj {P Q : hProp} : P ∨ (P ∧ Q) <-> P.
Proof.
  split.
  - apply hinhuniv; intros hPPQ.
    induction hPPQ as [hP|hPQ].
    + exact hP.
    + exact (pr1 hPQ).
  - intros hP; apply (hinhpr (ii1 hP)).
Defined.

Lemma logeq_disj_empty {P : hProp} : ∅ ∨ P <-> P.
Proof.
split.
  - apply hinhuniv; intros hPPQ.
    induction hPPQ as [hF|hP].
    + induction hF.
    + exact hP.
  - intros hP; apply (hinhpr (ii2 hP)).
Defined.
