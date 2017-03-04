Require Export UniMath.MoreFoundations.Notations.

Lemma logeq_dec {X Y} : (X <-> Y) -> decidable X -> decidable Y.
Proof.
  intros iff decX. induction iff as [XtoY YtoX].
  induction decX as [x|nx].
  - now apply ii1, XtoY.
  - now apply ii2, (negf YtoX).
Defined.

Definition decidable_prop (X:hProp) := hProppair (decidable X) (isapropdec X (pr2 X)).

(* override LEM of Foundations/Propositions.v, to make an hProp: *)
Definition LEM : hProp := ∀ P : hProp, decidable_prop P.
