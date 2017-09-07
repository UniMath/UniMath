Require Export UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.

Lemma retract_dec {X Y} (f : X -> Y) (g : Y -> X) (h : f ∘ g ~ idfun Y) : isdeceq X -> isdeceq Y.
Proof.
  intros i y y'. induction (i (g y) (g y')) as [eq|ne].
  - apply ii1. exact (! h y @ maponpaths f eq @ h y').
  - apply ii2. intro p. apply ne. exact (maponpaths g p).
Defined.

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
