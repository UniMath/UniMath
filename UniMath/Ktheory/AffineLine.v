(** * Construction of affine lines *)

Unset Automatic Introduction.
Require Import algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Notation ℕ := nat.
Notation ℤ := hzaddabgr.
Definition ℕtoℤ (n:ℕ) : ℤ := nattohz n.

Definition zero := ℕtoℤ 0.
Definition one := ℕtoℤ 1.

Variable T : Torsor ℤ.

Local Notation "n + x" := (ac_mult _ (n%hz:ℤ) x) : action_scope.
Local Notation "n - m" := (quotient _ n m) : action_scope.

Definition target_paths {Y} (f:T->Y) := forall t, f t==f(one + t).

Definition gHomotopy {Y} (f:T->Y) (s:target_paths f) y (h:nullHomotopyFrom f y) :=
  forall n, h(one + n) == h n @ s n.

Definition GHomotopy {Y} (f:T->Y) (s:target_paths f) y := total2 (gHomotopy f s y).

Definition GuidedHomotopy {Y} (f:T->Y) (s:target_paths f) := total2 (GHomotopy f s).

Definition ℕpath_inverse_to_rightℕ := coprod unit (coprod ℕ ℕ).
Definition p0 : ℕpath_inverse_to_rightℕ := inl tt.
Definition inj (n:ℕ) : ℕpath_inverse_to_rightℕ := inr (inl n).
Definition inj' (n:ℕ) : ℕpath_inverse_to_rightℕ := inr (inr n).

Definition ℕpath_inverse_to_rightℕtoT (t0:T) (w:ℕpath_inverse_to_rightℕ) : T.
Proof. intros. destruct w as [[]|[m|m']]. 
       { exact t0. }
       { exact (ℕtoℤ(S m) + t0). } { exact (- ℕtoℤ(S m') + t0). } Defined.

Definition Ttoℕpath_inverse_to_rightℕ (t0 t:T) : ℕpath_inverse_to_rightℕ.
Proof. intros. set (z := t - t0). destruct (isdeceqhz z zero) as [i|ne].
       { exact p0. }
       { destruct (hzneqchoice _ _ ne).
         { exact (inj (S (hzabsval z))). }
         { exact (inj' (S (hzabsval z))). } } Defined.

Definition isolate_t0_in_T (t0:T) : weq ℕpath_inverse_to_rightℕ T.
Proof. intros. refine (ℕpath_inverse_to_rightℕtoT t0,,gradth _ (Ttoℕpath_inverse_to_rightℕ t0) _ _).
       { intro w. induction w as [[]|p]. 
         { simpl.
           unfold Ttoℕpath_inverse_to_rightℕ.
           destruct (isdeceqhz (t0 - t0) zero) as [i|ne].
           { reflexivity. }
           { destruct (hzneqchoice (t0 - t0) zero ne).
             { apply fromempty; clear h. apply ne; clear ne.
               apply (quotient_1 _ t0). }
             { apply fromempty; clear h. apply ne; clear ne.
               apply (quotient_1 _ t0). } } }
         { destruct p as [n|n'].
           { simpl. unfold Ttoℕpath_inverse_to_rightℕ. 
             destruct (isdeceqhz (ℕtoℤ (S n) * t0 - t0) zero).
             { apply fromempty. apply (negpathssx0 n).
               apply (invmaponpathsincl _ isinclnattohz (S n) 0).
               exact (! quotient_mult _ (ℕtoℤ (S n)) t0 @ i). }
             { admit. } }
           { admit. } } }
       { admit. }
Defined.

Definition isolate0 {P:T->Type} (t0:T) : 
  weq (forall n, P n) 
      (dirprod (P t0) 
               (dirprod (forall n, P   (ℕtoℤ (S n) + t0))
                        (forall n, P (- ℕtoℤ (S n) + t0)))).
Proof. intros. intermediate_weq (forall n, P (isolate_t0_in_T t0 n)).
       { apply weqonsecbase. }
       intermediate_weq (
         dirprod (forall t, P (isolate_t0_in_T t0 (inl t)))
                 (forall w, P (isolate_t0_in_T t0 (inr w)))).
       { apply weqsecovercoprodtoprod. } apply weqdirprodf. 
       { apply weqsecoverunit. } { apply weqsecovercoprodtoprod. } Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/AffineLine.vo"
End:
*)
