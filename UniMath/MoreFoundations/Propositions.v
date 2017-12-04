Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.DecidablePropositions.

Local Open Scope logic.

Lemma ishinh_irrel {X:UU} (x:X) (x':∥X∥) : hinhpr x = x'.
Proof.
  apply proofirrelevance. apply propproperty.
Defined.

Corollary squash_to_hProp {X:UU} {Q:hProp} : ∥ X ∥ -> (X -> Q) -> Q.
Proof. intros h f. exact (hinhuniv f h). Defined.

Lemma hdisj_impl_1 {P Q : hProp} : P∨Q -> (Q->P) -> P.
Proof.
  intros o f. apply (squash_to_hProp o).
  intros [p|q].
  - exact p.
  - exact (f q).
Defined.

Lemma hdisj_impl_2 {P Q : hProp} : P∨Q -> (P->Q) -> Q.
Proof.
  intros o f. apply (squash_to_hProp o).
  intros [p|q].
  - exact (f p).
  - exact q.
Defined.

Definition weqlogeq (P Q : hProp) : (P = Q) ≃ (P ⇔ Q).
Proof.
  intros.
  apply weqimplimpl.
  - intro e. induction e. apply isrefl_logeq.
  - intro c. apply hPropUnivalence.
    + exact (pr1 c).
    + exact (pr2 c).
  - apply isasethProp.
  - apply propproperty.
Defined.

Lemma decidable_proof_by_contradiction {P:hProp} : decidable P -> ¬ ¬ P -> P.
Proof.
  intros dec nnp. induction dec as [p|np].
  - exact p.
  - apply fromempty. exact (nnp np).
Defined.

Lemma proof_by_contradiction {P:hProp} : LEM -> ¬ ¬ P -> P.
Proof.
  intro lem.
  exact (decidable_proof_by_contradiction (lem P)).
Defined.

Lemma dneg_elim_to_LEM : (∏ P:hProp, ¬ ¬ P -> P) -> LEM.
(* a converse for Lemma dneg_LEM *)
Proof.
  intros dne. intros P. simple refine (dne (_,,_) _).
  simpl. intros n.
  assert (q : ¬ (P ∨ ¬ P)).
  { now apply weqnegtonegishinh. }
  assert (r := fromnegcoprod_prop q).
  exact (pr2 r (pr1 r)).
Defined.

Lemma negforall_to_existsneg {X:UU} (P:X->hProp) : LEM -> (¬ ∀ x, P x) -> (∃ x, ¬ (P x)).
(* was omitted from the section on "Negation and quantification" in Foundations/Propositions.v *)
Proof.
  intros lem nf. apply (proof_by_contradiction lem); intro c. use nf; clear nf. intro x.
  assert (q := neghexisttoforallneg _ c x); clear c; simpl in q.
  exact (proof_by_contradiction lem q).
Defined.

Lemma negimpl_to_conj (P Q:hProp) : LEM -> ( ¬ (P ⇒ Q) -> P ∧ ¬ Q ).
Proof.
  intros lem ni. assert (r := negforall_to_existsneg _ lem ni); clear lem ni.
  apply (squash_to_hProp r); clear r; intros [p nq]. exact (p,,nq).
Defined.

Definition hrel_set (X : hSet) : hSet := hSetpair (hrel X) (isaset_hrel X).

Lemma isaprop_assume_it_is {X : UU} : (X -> isaprop X) -> isaprop X.
Proof.
  intros f. apply invproofirrelevance; intros x y.
  apply proofirrelevance. now apply f.
Defined.

Lemma isaproptotal2 {X : UU} (P : X → UU) :
  isPredicate P →
  (∏ x y : X, P x → P y → x = y) →
  isaprop (∑ x : X, P x).
Proof.
  intros HP Heq.
  apply invproofirrelevance.
  intros [x p] [y q].
  induction (Heq x y p q).
  induction (iscontrpr1 (HP x p q)).
  apply idpath.
Defined.

Lemma squash_rec {X : UU} (P : ∥ X ∥ -> hProp) : (∏ x, P (hinhpr x)) -> (∏ x, P x).
Proof.
  intros xp x'. simple refine (hinhuniv _ x'). intro x.
  assert (q : hinhpr x = x').
  { apply propproperty. }
  induction q. exact (xp x).
Defined.

Lemma logeq_if_both_true (P Q : hProp) : P -> Q -> ( P ⇔ Q ).
Proof.
  intros p q.
  split.
  - intros _. exact q.
  - intros _. exact p.
Defined.

Lemma logeq_if_both_false (P Q : hProp) : ¬P -> ¬Q -> ( P ⇔ Q ).
Proof.
  intros np nq.
  split.
  - intros p. apply fromempty. exact (np p).
  - intros q. apply fromempty. exact (nq q).
Defined.

Definition proofirrelevance_hProp (X : hProp) : isProofIrrelevant X
  := proofirrelevance X (propproperty X).

Ltac induction_hProp x y := induction (proofirrelevance_hProp _ x y).

Definition iscontr_hProp (X:UU) : hProp := hProppair (iscontr X) (isapropiscontr X).

Notation "'∃!' x .. y , P"
  := (iscontr_hProp (∑ x, .. (∑ y, P) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
(* type this in emacs in agda-input method with \ex ! *)


(** Various algebraic properties of hProp *)
Section hProp_logic.

(** We first state the algebraic properties as bi-implications *)

(* This is already in Foundations/Propositions.v *)
(* Lemma islogeqcommhdisj {P Q : hProp} : hdisj P Q <-> hdisj Q P. *)

Lemma islogeqassochconj {P Q R : hProp} : (P ∧ Q) ∧ R <-> P ∧ (Q ∧ R).
Proof.
split.
- intros PQR.
  exact (pr1 (pr1 PQR),,(pr2 (pr1 PQR),,pr2 PQR)).
- intros PQR.
  exact ((pr1 PQR,,pr1 (pr2 PQR)),,pr2 (pr2 PQR)).
Defined.

Lemma islogeqcommhconj {P Q : hProp} : P ∧ Q <-> Q ∧ P.
Proof.
split.
- intros PQ.
  exact (pr2 PQ,,pr1 PQ).
- intros QP.
  exact (pr2 QP,,pr1 QP).
Defined.

Lemma islogeqassochdisj {P Q R : hProp} : (P ∨ Q) ∨ R <-> P ∨ (Q ∨ R).
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

Lemma islogeqhconj_absorb_hdisj {P Q : hProp} : P ∧ (P ∨ Q) <-> P.
Proof.
split.
- intros hPPQ; apply (pr1 hPPQ).
- intros hP.
  split; [ apply hP | apply (hinhpr (ii1 hP)) ].
Defined.

Lemma islogeqhdisj_absorb_hconj {P Q : hProp} : P ∨ (P ∧ Q) <-> P.
Proof.
split.
- apply hinhuniv; intros hPPQ.
  induction hPPQ as [hP|hPQ].
  + exact hP.
  + exact (pr1 hPQ).
- intros hP; apply (hinhpr (ii1 hP)).
Defined.

Lemma islogeqhfalse_hdisj {P : hProp} : ∅ ∨ P <-> P.
Proof.
split.
- apply hinhuniv; intros hPPQ.
  induction hPPQ as [hF|hP].
  + induction hF.
  + exact hP.
- intros hP; apply (hinhpr (ii2 hP)).
Defined.

Lemma islogeqhhtrue_hconj {P : hProp} : htrue ∧ P <-> P.
Proof.
split.
- intros hP; apply (pr2 hP).
- intros hP.
  split; [ apply tt | apply hP ].
Defined.


(** We now turn these into equalities using univalence for propositions *)
Lemma isassoc_hconj (P Q R : hProp) : ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)).
Proof.
now apply hPropUnivalence; apply islogeqassochconj.
Qed.

Lemma iscomm_hconj (P Q : hProp) : (P ∧ Q) = (Q ∧ P).
Proof.
now apply hPropUnivalence; apply islogeqcommhconj.
Qed.

Lemma isassoc_hdisj (P Q R : hProp) : ((P ∨ Q) ∨ R) = (P ∨ (Q ∨ R)).
Proof.
now apply hPropUnivalence; apply islogeqassochdisj.
Qed.

Lemma iscomm_hdisj (P Q : hProp) : (P ∨ Q) = (Q ∨ P).
Proof.
now apply hPropUnivalence; apply islogeqcommhdisj.
Qed.

Lemma hconj_absorb_hdisj (P Q : hProp) : (P ∧ (P ∨ Q)) = P.
Proof.
now apply hPropUnivalence; apply islogeqhconj_absorb_hdisj.
Qed.

Lemma hdisj_absorb_hconj (P Q : hProp) : (P ∨ (P ∧ Q)) = P.
Proof.
now apply hPropUnivalence; apply islogeqhdisj_absorb_hconj.
Qed.

Lemma hfalse_hdisj (P : hProp) : (∅ ∨ P) = P.
Proof.
now apply hPropUnivalence; apply islogeqhfalse_hdisj.
Qed.

Lemma htrue_hconj (P : hProp) : (htrue ∧ P) = P.
Proof.
now apply hPropUnivalence; apply islogeqhhtrue_hconj.
Qed.

End hProp_logic.