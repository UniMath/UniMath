(**

Definition natural number objects (NNO's)

This is related to the initial algebra definition in FunctorAlgebras.v

Written by: Anders Mörtberg, 2018

*)
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

Section nno.

Context {C : precategory} (TC : Terminal C).

Local Notation "1" := TC.

Definition isNNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧) : hProp.
Proof.
use tpair.
- exact (∏ (a : C) (q : C ⟦ 1, a ⟧) (f : C ⟦ a, a ⟧),
         ∃! u : C ⟦ n, a ⟧, (z · u = q) × (s · u = u · f)).
- abstract (repeat (apply impred_isaprop; intros); apply isapropiscontr).
Defined.

Definition NNO : UU :=
  ∑ (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧), isNNO n z s.

Definition NNObject (n : NNO) : C := pr1 n.
Coercion NNObject : NNO >-> ob.

Definition zeroNNO (n : NNO) : C ⟦1,n⟧ := pr1 (pr2 n).
Definition sucNNO (n : NNO) : C ⟦n,n⟧ := pr1 (pr2 (pr2 n)).

Lemma isNNO_NNO (n : NNO) : isNNO n (zeroNNO n) (sucNNO n).
Proof.
exact (pr2 (pr2 (pr2 n))).
Qed.

Definition mk_NNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧)
 (h : isNNO n z s) : NNO := (n,,z,,s,,h).

Definition hasNNO : hProp := ∥ NNO ∥.

End nno.
