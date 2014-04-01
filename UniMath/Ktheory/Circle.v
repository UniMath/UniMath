(** * Construction of the circle *)

Unset Automatic Introduction.
Require Import AffineLine algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Local Notation "g + x" := (ac_mult _ g x) : action_scope.
Notation ℕ := nat.
Notation ℤ := hzaddabgr.
Definition circle := B ℤ.

Theorem loops_circle : weq (Ω circle) ℤ.
Proof. apply loopsBG. Defined.

Definition circle_loop := invmap loops_circle 1 : Ω circle.

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

Definition circle_map {Y} {y:Y} (l:y==y) : circle -> Y.
Proof. intros ? ? ? T. simpl in T.
       exact (affine_line_value (fun t:T => y) (fun t:T => l)). Defined.

Definition circle_map_check_values {Y} {y:Y} (l:y==y) : 
  circle_map l (basepoint circle) == y.
Proof. reflexivity.              (* don't change the proof *)
Defined.

Definition check_paths2 {Y} {y:Y} (l:y==y) :
  ap (affine_line_map (T:=trivialTorsor ℤ) (fun _ => y) (fun _ => l))
     (affine_line_path
        (affine_line_point (trivialTorsor ℤ))
        (add_one (affine_line_point (trivialTorsor ℤ)))) == l.
Proof. intros. apply check_paths_any. Defined.

Definition circle_map_check_paths {Y} {y:Y} (l:y==y) : 
  ap (circle_map l) circle_loop == l.
Proof. intros.
       set (T := basepoint circle); simpl in T.
       set (t0 := 0).
       set (n0 := pr1 (pr2 T)).
       change (pr1 T) with (underlyingAction T) in n0.
       change (pr1 (pr2 T)) with (squash_element 0) in n0.
       set (f := fun t:T => y). 
       set (s := fun t:T => l).
       assert (a := AffineLine.check_paths_any f s t0).
       change (s t0) with l in a.
       assert (r := ! ap_pr1_pr2 circle_loop).
       change (pr1 (pr2 (basepoint circle))) with n0 in r.
       set (r1 := path_end r).
       change (pr1 (basepoint circle)) with (underlyingAction T) in r1.
       unfold path_end in r1.
       (* to do: identify r1, or redefine circle_loop so it makes that possible *)
       

       set (r2 := affine_line_map f s r1).
       unfold affine_line_map,r1,map in r2. 


       Check check_paths_any f s t0.

       admit.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/Circle.vo"
End:
*)
