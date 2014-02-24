Unset Automatic Introduction.

Inductive N := O : N | S : N -> N.

Fixpoint plus (m n : N) : N.
  intros.
  destruct n as [ | n ].
  - exact m.
  - exact (S (plus m n)).
Defined.

Eval compute in plus (S(S(S O))) (S(S O)).

Inductive identity {X} (x:X) : X -> Type := 
  idpath : identity x x.

Notation "x == y" := (identity x y) (at level 70).

Definition reverse {X} {x y:X} (e:x==y) : y==x.
  intros.
  induction e.
  exact (idpath x).
Defined.

Lemma a n : plus O n == plus n O.
Proof. intros.
       induction n as [ | n IH ].
       - exact (idpath O).
       - simpl.
         assert(e := reverse IH).
         clear IH.
         induction e.
         simpl.
         exact (idpath (S n)).
Defined.
