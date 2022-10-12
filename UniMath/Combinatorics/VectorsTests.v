(** * Tests for vectors as iterated products. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Local Open Scope stn.

Section Tests_el.

  Context {A : UU} {a b c d:A}.

  Let v := vcons a (vcons b (vcons c (vcons d vnil))).

  Goal el v (●0) = a. reflexivity. Qed.
  Goal el v (●1) = b. reflexivity. Qed.
  Goal el v (●2) = c. reflexivity. Qed.
  Goal el v (●3) = d. reflexivity. Qed.

  Goal make_vec (el v) = v. reflexivity. Qed.

  Let f : ⟦ 4 ⟧ → A := Eval compute in (el v).

  Goal (el (make_vec f) = f). reflexivity. Qed.

End Tests_el.

Section Test_vec_foldr.

  Context {A B : UU} (f : A -> B -> B) (b : B) (p q r : A).

  Let v := vcons p (vcons q (vcons r vnil)).

  Eval compute in vec_foldr f b v.

  Goal vec_foldr f b v = f p (f q (f r b)). reflexivity. Qed.

End Test_vec_foldr.

Section Test_vec_foldr1.

  Context {A : UU} (f : A -> A -> A)  (p q r t : A).

  Let v := vcons p (vcons q (vcons r (vcons t vnil))).

  Eval compute in vec_foldr1 f v.

  Goal vec_foldr1 f v = f p (f q (f r t)). reflexivity. Qed.

End Test_vec_foldr1.

Section Test_vec_append.

  Context {A : UU} {a b c d e : A}.

  Let u := vcons a (vcons b (vcons c vnil)).
  Let v := vcons d (vcons e vnil).
  Let w := vcons a (vcons b (vcons c (vcons d (vcons e vnil)))).

  Eval compute in vec_append u v.

  Goal vec_append u v = w. reflexivity. Qed.

End Test_vec_append.
