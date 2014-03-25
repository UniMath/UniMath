(** * Construction of affine lines *)

Unset Automatic Introduction.
Require Import algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Notation NN := nat.
Notation ZZ := hzaddabgr.
Definition toZZ (n:NN) : ZZ := nattohz n.
Definition zero := toZZ 0.
Definition one := toZZ 1.

Open Scope hz_scope.

Lemma ZZRecursionUniq (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  iscontr (total2 (fun 
          f:forall i, P i => dirprod 
            (f zero==p0) (dirprod
            (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
            (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n)))))).
Proof. intros.
       admit.
Defined.

Lemma A (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  weq (total2 (fun 
          f:forall i, P i => dirprod 
            (f zero==p0) (dirprod
            (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
            (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n))))))
      (@hfiber
         (total2 (fun 
             f:forall i, P i => dirprod 
               (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
               (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n)))))
         (P zero)
         (fun fh => pr1 fh zero)
         p0).
Proof. intros.
       refine (weqpair _ (gradth _ _ _ _)).
       { intros [f [h0 h]]. exact ((f,,h),,h0). }
       { intros [[f h] h0]. exact (f,,(h0,,h)). }
       { intros [f [h0 h]]. reflexivity. }
       { intros [[f h] h0]. reflexivity. } Defined.

Lemma ZZRecursionEquiv (P:ZZ->Type) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  weq (total2 (fun 
          f:forall i, P i => dirprod 
            (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
            (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n)))))
      (P zero).
Proof. intros. exists (fun f => pr1 f zero). intro p0.
       apply (iscontrweqf (A _ _ _ _)). apply ZZRecursionUniq. Defined.

Notation "n + x" := (ac_mult _ (n%hz:ZZ) x) : action_scope.
Notation "n - m" := (quotient _ n m) : action_scope.
Open Scope action_scope.

Definition swequiv {X Y} (f:weq X Y) {x y} : y == f x -> invweq f y == x.
Proof. intros ? ? ? ? ? p. exact (ap (invweq f) p @ homotinvweqweq f x). Defined.

Definition swequiv' {X Y} (f:weq X Y) {x y} : invweq f y == x -> y == f x.
Proof. intros ? ? ? ? ? p. exact (! homotweqinvweq f y @ ap f p). Defined.

Definition ZZTorsorRecursionEquiv {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t))) :
  forall t,
  weq (total2 (fun 
          f:forall t, P t => 
            forall t, f (one + t) == IH t (f t)))
      (P t).
Proof. intros.
       exists (fun fh => pr1 fh t).
       set (w := triviality_isomorphism T t).
       set (P' := funcomp w P).
       assert (k : forall n, w (toZZ (S n)) == one + w (toZZ n)).
       { intros. simpl. rewrite nattohzandS. unfold right_mult, one. unfold toZZ.
         rewrite nattohzand1. apply act_assoc. }
       admit.
Defined.

Definition ZZTorsorRecursion {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t t':T) :
  weq (P t) (P t').
Proof. intros.
       exact (weqcomp (invweq (ZZTorsorRecursionEquiv P IH t))
                      (ZZTorsorRecursionEquiv P IH t')). Defined.  

Definition target_paths {Y} {T:Torsor ZZ} (f:T->Y) := forall t, f t==f(one + t).

Definition GHomotopy {Y} {T:Torsor ZZ} (f:T->Y) (s:target_paths f) := fun 
        y:Y => total2 (fun 
        h:nullHomotopyFrom f y => 
          forall n, h(one + n) == h n @ s n).

Definition GuidedHomotopy {Y} {T:Torsor ZZ} (f:T->Y) (s:target_paths f) := 
  total2 (GHomotopy f s).



(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/AffineLine.vo"
End:
*)
