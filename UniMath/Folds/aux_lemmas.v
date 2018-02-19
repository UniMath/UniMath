
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.


Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (λ a, B a)))
           (a : A) (H : B a) : a = pr1 (pr1 isc).
Proof.
  set (Hi := tpair _ a H).
  apply (maponpaths pr1 (pr2 isc Hi)).
Defined.
