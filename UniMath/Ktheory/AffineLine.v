(** * Construction of affine lines *)

Unset Automatic Introduction.
Require Import algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Definition ZZ := hzaddabgr.
Definition toZZ (n:nat) : ZZ := nattohz n.
Definition zero := toZZ 0.
Definition one := toZZ 1.

Open Scope hz_scope.

Lemma hzminusplus (x y:hz) : -(x+y) == (-x) + (-y). (* move to u00 *)
Proof. intros. apply (hzplusrcan _ _ (x+y)). rewrite hzlminus. 
       rewrite (hzpluscomm (-x)). rewrite (hzplusassoc (-y)).
       rewrite <- (hzplusassoc (-x)). rewrite hzlminus. rewrite hzplusl0.
       rewrite hzlminus. reflexivity. Defined.

Definition ZZRecursionData0 (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) := fun 
          f:forall i, P i => dirprod 
            (f zero==p0) (dirprod
            (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
            (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n)))).

Definition ZZRecursionData (P:ZZ->Type)
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) := fun 
             f:forall i, P i => dirprod 
               (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
               (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n))).

Lemma ZZRecursionUniq (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  iscontr (total2 (ZZRecursionData0 P p0 IH IH')).
Proof. intros.
       admit.
Defined.

Lemma A (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  weq (total2 (ZZRecursionData0 P p0 IH IH'))
      (@hfiber
         (total2 (ZZRecursionData P IH IH'))
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
  weq (total2 (ZZRecursionData P IH IH'))
      (P zero).
Proof. intros. exists (fun f => pr1 f zero). intro p0.
       apply (iscontrweqf (A _ _ _ _)). apply ZZRecursionUniq. Defined.

Notation "n + x" := (ac_mult _ n x) : action_scope.
Notation "n - m" := (quotient _ n m) : action_scope.
Open Scope action_scope.

Definition swequiv {X Y} (f:weq X Y) {x y} : y == f x -> invweq f y == x.
Proof. intros ? ? ? ? ? p. exact (ap (invweq f) p @ homotinvweqweq f x). Defined.

Definition swequiv' {X Y} (f:weq X Y) {x y} : invweq f y == x -> y == f x.
Proof. intros ? ? ? ? ? p. exact (! homotweqinvweq f y @ ap f p). Defined.

Definition hzabsvalnat n : hzabsval (nattohz n) == n. (* move to uu0 *)
Proof. intros.
       refine (setquotunivcomm (binopeqrelabgrfrac (rigaddabmonoid natcommrig)) natset hzabsvalint hzabsvalintcomp _ @ _).
       unfold hzabsvalint; simpl. destruct (natgthorleh n 0).
       { apply natminuseqn. } { exact (! (natleh0tois0 _ h)). }
Defined.

Definition negpos : weq ZZ (coprod nat nat). (* ZZ = (-inf,-1) + (0,inf) *)
Proof. refine (weqpair _ (gradth _ _ _ _)).
       { intro i. induction (hzlthorgeh i zero).
         { exact (inl (hzabsval i - 1)%nat). }
         { exact (inr (hzabsval i)). } }
       { intros [n'|n]. { exact (natnattohz 0 (S n')). } { exact (toZZ n). } }
       { simpl. intro i. 
         induction (hzlthorgeh i zero) as [e|e']; simpl.
         { assert (a := hzabsvallth0 e).
           admit. }
         { exact (hzabsvalgeh0 e'). } }
       { intros [n'|n].
         { simpl. rewrite natminuseqn. reflexivity. }
         { simpl. rewrite hzabsvalnat. reflexivity. } }
Defined.

Definition ZZTorsorRecursionEquiv {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t))) :
  forall t,
  weq (total2 (fun 
          f:forall t, P t => 
            forall t, f (one + t) == IH t (f t)))
      (P t).
Proof. intros.
       (* exists (fun fh => pr1 fh t). *)
       set (w := triviality_isomorphism T t).
       assert (k1 : forall n, one + w (toZZ n) == w (toZZ (S n))).
       { intros. simpl. rewrite nattohzandS. unfold right_mult, one. unfold toZZ.
         rewrite nattohzand1. apply pathsinv0. apply act_assoc. }
       set (l1 := (fun n => eqweqmap (ap P (k1 n))) 
                : forall n, weq (P(one + w (toZZ n))) (P(w(toZZ (S n))))).
       assert (k2: forall n, one + w (- toZZ (S n)) == w (- toZZ n)).
       { intros; simpl. unfold one. unfold toZZ. rewrite nattohzand1.
         rewrite nattohzandS. rewrite hzminusplus. unfold right_mult.
         rewrite <- (ac_assoc _ one). rewrite <- (hzplusassoc one).
         rewrite (hzpluscomm one). rewrite hzlminus. rewrite hzplusl0.
         reflexivity. }
       set (l2 := (fun n => eqweqmap (ap P (k2 n)))
                   : forall n, weq (P(one + w (- toZZ (S n)))) (P(w(-toZZ n)))).
       set (P' := fun i => P(w i)).
       set (ih := fun n => weqcomp (IH (w (toZZ n))) (l1 n)).
       set (ih':= fun n => invweq (weqcomp (IH (w (- toZZ (S n)))) (l2 n))).
       assert (G := ZZRecursionEquiv P' ih ih'); simpl in G.
       unfold P' in G; simpl in G.
       assert( e : right_mult t zero == t ). { apply act_unit. }
       rewrite e in G; clear e.
       unfold ZZRecursionData in G.
       refine (weqcomp _ G).
       clear G ih ih' P'.
       refine (weqbandf (weqonsecbase _ w) _ _ _).
       intro f.
       intermediate_weq (forall i, f (one + w i) == (IH (w i)) (f (w i))).
       { exact (weqonsecbase _ w). }
       change (set_to_type (trivialTorsor ZZ)) with (set_to_type ZZ).
         

         

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
