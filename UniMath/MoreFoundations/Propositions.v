Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Tactics.
Require Export UniMath.MoreFoundations.DecidablePropositions.
Require Export UniMath.MoreFoundations.LogicalEquivalence.Props.

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

(** We now turn bi-implications into equalities using univalence for
    propositions *)
Lemma isassoc_hconj (P Q R : hProp) : ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)).
Proof.
  apply hPropUnivalence; apply hequiv_assoc_conj.
Qed.

Lemma iscomm_hconj (P Q : hProp) : (P ∧ Q) = (Q ∧ P).
Proof.
  apply hPropUnivalence; apply hequiv_comm_conj.
Qed.

Lemma isassoc_hdisj (P Q R : hProp) : ((P ∨ Q) ∨ R) = (P ∨ (Q ∨ R)).
Proof.
  apply hPropUnivalence; apply logeq_assoc_disj.
Qed.

Lemma iscomm_hdisj (P Q : hProp) : (P ∨ Q) = (Q ∨ P).
Proof.
  apply hPropUnivalence; apply islogeqcommhdisj.
Qed.

Lemma hconj_absorb_hdisj (P Q : hProp) : (P ∧ (P ∨ Q)) = P.
Proof.
  apply hPropUnivalence; apply logeq_conj_with_disj.
Qed.

Lemma hdisj_absorb_hconj (P Q : hProp) : (P ∨ (P ∧ Q)) = P.
Proof.
  apply hPropUnivalence; apply logeq_disj_with_conj.
Qed.

Lemma hfalse_hdisj (P : hProp) : (∅ ∨ P) = P.
Proof.
  apply hPropUnivalence; apply logeq_disj_empty.
Qed.

Lemma htrue_hconj (P : hProp) : (htrue ∧ P) = P.
Proof.
  apply hPropUnivalence; apply hequiv_conj_true.
Qed.

End hProp_logic.
