
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.


Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (λ a, B a)))
           (a : A) (H : B a) : a = pr1 (pr1 isc).
Proof.
  set (Hi := tpair _ a H).
  apply (maponpaths pr1 (pr2 isc Hi)).
Defined.

Lemma dirprodpath (A B : UU) (x y : dirprod A B) :
  pr1 x = pr1 y -> pr2 x = pr2 y -> x = y.
Proof.
  intros H1 H2.
  destruct x; destruct y. simpl in *.
  apply pathsdirprod; assumption.
Defined.
