
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.



Lemma path_to_ctr (A : UU) (B : A → UU) (isc : iscontr (total2 (λ a, B a))) 
           (a : A) (H : B a) : a == pr1 (pr1 isc).
Proof.
  set (Hi := tpair _ a H).
  apply (maponpaths pr1 (pr2 isc Hi)).
Defined.
