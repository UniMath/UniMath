Require Export UniMath.MoreFoundations.Notations.

Local Open Scope logic.

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

Definition hrel_set (X : hSet) : hSet := hSetpair (hrel X) (isaset_hrel X).

Lemma isaprop_assume_it_is {X : UU} : (X -> isaprop X) -> isaprop X.
Proof.
  intros f. apply invproofirrelevance; intros x y.
  apply proofirrelevance. now apply f.
Defined.

Lemma squash_rec {X : UU} (P : ∥ X ∥ -> hProp) : (∏ x, P (hinhpr x)) -> (∏ x, P x).
Proof.
  intros xp x'. simple refine (hinhuniv _ x'). intro x.
  assert (q : hinhpr x = x').
  { apply propproperty. }
  induction q. exact (xp x).
Defined.
