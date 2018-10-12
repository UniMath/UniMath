Require Import UniMath.Foundations.All.

Lemma wma_dneg {X} P : ¬¬ P -> (P -> ¬ X) -> ¬ X.
(* when proving a negation, we may undo a double negation *)
Proof.
  intros dnp p.
  apply dnegnegtoneg.
  assert (q := dnegf p); clear p.
  apply q; clear q.
  apply dnp.
Defined.

Lemma dneg_decidable P : ¬¬ decidable P.
(* it's not false that a type is decidable *)
Proof.
  intros ndec.
  unfold decidable in ndec.
  assert (q := fromnegcoprod ndec); clear ndec.
  contradicts (pr1 q) (pr2 q).
Defined.

Lemma wma_decidable {X} P : (decidable P -> ¬ X) -> ¬ X.
(* when proving a negation, we may assume a type is decidable *)
Proof.
  apply (wma_dneg (decidable P)).
  apply dneg_decidable.
Defined.

Open Scope logic.

Lemma negforall_to_existsneg' {X} (P:X->Type) : (¬ ∏ x, ¬¬ (P x)) -> ¬¬ (∃ x, ¬ (P x)).
(* compare with [negforall_to_existsneg], which uses LEM *)
Proof.
  intros nf c. use nf; clear nf. intro x.
  assert (q := neghexisttoforallneg _ c x); clear c; simpl in q.
  exact q.
Defined.
