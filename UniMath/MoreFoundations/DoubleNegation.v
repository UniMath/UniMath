Require Import UniMath.Foundations.All.

(** When proving a negation, we may undo a double negation. *)
Lemma wma_dneg {X} P : ¬¬ P -> (P -> ¬ X) -> ¬ X.
Proof.
  intros dnp p.
  apply dnegnegtoneg.
  assert (q := dnegf p); clear p.
  apply q; clear q.
  apply dnp.
Defined.

(** It's not false that a type is decidable. *)
Lemma dneg_decidable P : ¬¬ decidable P.
Proof.
  intros ndec.
  unfold decidable in ndec.
  assert (q := fromnegcoprod ndec); clear ndec.
  contradicts (pr1 q) (pr2 q).
Defined.

(** When proving a negation, we may assume a type is decidable. *)
Lemma wma_decidable {X} P : (decidable P -> ¬ X) -> ¬ X.
Proof.
  apply (wma_dneg (decidable P)).
  apply dneg_decidable.
Defined.

Local Open Scope logic.

(** Compare with [negforall_to_existsneg], which uses LEM instead. *)
Lemma negforall_to_existsneg' {X} (P:X->Type) : (¬ ∏ x, ¬¬ (P x)) -> ¬¬ (∃ x, ¬ (P x)).
Proof.
  intros nf c. use nf; clear nf. intro x.
  assert (q := neghexisttoforallneg _ c x); clear c; simpl in q.
  exact q.
Defined.
