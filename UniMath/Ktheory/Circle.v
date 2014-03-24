(** * Construction of the circle *)

Unset Automatic Introduction.
Require Import AffineLine algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Notation ℕ := nat.
Notation ℤ := hzaddabgr.
Definition circle := B ℤ.

Theorem loops_circle : weq (Ω circle) ℤ.
Proof. apply loopsBG. Defined.

(** * Powers of paths *) 

Definition loop_power_nat {Y} {y:Y} (l:y==y) (n:ℕ) : y==y.
Proof. intros. induction n as [|n p]. 
       { exact (idpath _). } { exact (p@l). } Defined.

Local Notation "l ^ n" := (loop_power_nat l n) : paths_nat_scope.

Definition loop_power {Y} {y:Y} (l:y==y) (n:ℤ) : y==y.
Proof. intros. assert (m := loop_power_nat l (hzabsval n)).
       destruct (hzlthorgeh n 0%hz). { exact (!m). } { exact m. } Defined.

Delimit Scope paths_scope with paths.
Open Scope paths_scope.
Local Notation "l ^ n" := (loop_power l n) : paths_scope.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/Circle.vo"
End:
*)
