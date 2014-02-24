Unset Automatic Introduction.

Inductive N := O : N | S : N -> N.

Definition plus (m n : N) : N.
  intros.
  induction n.
  - exact m.
  - exact (S IHn).
Defined.

Eval compute in plus (S(S(S O))) (S(S O)).

Inductive identity {X} (x:X) : X -> Type := 
  id : identity x x.

Notation "x == y" := (identity x y) (at level 70).

Definition reverse {X} {x y:X} (e:x==y) : y==x.
  intros.
  induction e.
  exact (id x).
Defined.

Lemma a n : plus O n == plus n O.
Proof. intros.
       induction n.
       - exact (id O).
       - simpl.
         assert(e := reverse IHn).
         clear IHn.
         induction e.
         simpl.
         exact (id (S n)).
Defined.
