(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Nat.
Require Import UniMath.Algebra.Universal.Bool.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Section Nat.

Local Definition test1: stack2status (nat_succ :: nat_zero :: nil) = stackok 1 := idpath _.
Local Definition test2: stack2status(sigma := nat_signature) nil = stackok 0 := idpath _.
Local Definition test3: stack2status (nat_zero :: nat_zero :: nil) = stackok 2 := idpath _.
Local Definition test4: stack2status (nat_succ :: nil) = stackerror := idpath _.
Local Definition test5: term2stack (mkterm nat_succ (vcons (mkterm nat_zero vnil) vnil)) = nat_succ :: nat_zero :: nil := idpath _.

End Nat.

Section Bool.

Local Definition t_false: term := mkterm bool_false vnil.
Local Definition t_true: term := mkterm bool_true vnil.
Local Definition t1: term := mkterm bool_and (vcons t_true (vcons t_false vnil)).
Local Definition t2: term := mkterm bool_not (vcons t1 vnil).

Local Definition testb1: princ_op t1 = bool_and := idpath _.
Local Definition testb2: term2stack t2 = bool_not  :: bool_and :: bool_true :: bool_false :: nil := idpath _.

End Bool.
