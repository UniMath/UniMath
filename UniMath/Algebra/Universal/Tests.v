(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Nat.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.

Local Definition test1: s2ss (nat_succ :: nat_zero :: nil) = stackok 1 := idpath _.
Local Definition test2: s2ss(sigma := nat_signature) nil = stackok 0 := idpath _.
Local Definition test3: s2ss (nat_zero :: nat_zero :: nil) = stackok 2 := idpath _.
Local Definition test4: s2ss (nat_succ :: nil) = stackerror := idpath _.

Local Definition test5: (pr1 (term_op nat_succ (vcons (term_op nat_zero vnil) vnil))) = nat_succ :: nat_zero :: nil := idpath _.
