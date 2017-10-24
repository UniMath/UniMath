(** proofs that the statements of the axioms are propositions *)

Require Import UniMath.Foundations.PartD.

Lemma isaprop_univalenceStatement : isaprop univalenceStatement.
Proof.
  unfold univalenceStatement.
  apply impred_isaprop; intro X;
  apply impred_isaprop; intro Y.
  apply isapropisweq.
Defined.

Lemma isaprop_funextemptyStatement : isaprop funextemptyStatement.
Proof.
  unfold funextemptyStatement.
  apply impred_isaprop; intro X;
  apply impred_isaprop; intro f;
  apply impred_isaprop; intro g.
  generalize g; clear g.
  generalize f; clear f.
  change (isaset (X → ∅)).
  apply impred_isaset; intro x.
  apply isasetempty.
Defined.

Lemma isaprop_isweqtoforallpathsStatement : isaprop isweqtoforallpathsStatement.
Proof.
  unfold isweqtoforallpathsStatement.
  apply impred_isaprop; intro T;
  apply impred_isaprop; intro P;
  apply impred_isaprop; intro f;
  apply impred_isaprop; intro g.
  apply isapropisweq.
Defined.

Lemma isaprop_propositionalUnivalenceStatement : isaprop propositionalUnivalenceStatement.
Proof.
  unfold propositionalUnivalenceStatement.
  apply impred_isaprop; intro P;
  apply impred_isaprop; intro Q;
  apply impred_isaprop; intro i;
  apply impred_isaprop; intro j;
  apply impred_isaprop; intros _;
  apply impred_isaprop; intros _.
  apply (isofhlevelweqb 1 (univalence P Q)).
  fold isaprop.
  apply isapropweqtoprop.
  exact j.
Defined.

Lemma isaprop_funcontrStatement : isaprop funcontrStatement.
Proof.
  unfold funcontrStatement.
  apply impred_isaprop; intro X;
  apply impred_isaprop; intro P;
  apply impred_isaprop; intros _.
  apply isapropiscontr.
Defined.

Lemma isaprop_funextcontrStatement : isaprop funextcontrStatement.
Proof.
  unfold funextcontrStatement.
  apply impred_isaprop; intro T;
  apply impred_isaprop; intro P;
  apply impred_isaprop; intro g.
  apply isapropiscontr.
Defined.

(* end *)
