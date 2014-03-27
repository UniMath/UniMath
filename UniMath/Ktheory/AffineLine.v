(** * Construction of affine lines *)

Unset Automatic Introduction.
Require Import algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation Utilities.NatNotation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Definition ZZ := hzaddabgr.
Definition toZZ (n:nat) : ZZ := nattohz n.
Definition zero := toZZ 0.
Definition one := toZZ 1.

Open Scope hz_scope.

Definition hzabsvalnat n : hzabsval (natnattohz n 0) == n. (* move to hz.v *)
Proof. intros. unfold hzabsval. unfold setquotuniv. simpl.
       unfold hzabsvalint. simpl. destruct (natgthorleh n 0).
       { apply natminuseqn. } { exact (! (natleh0tois0 _ h)). } Defined.

Lemma hzsign_natnattohz m n : - natnattohz m n == natnattohz n m. (* move to hz.v *)
Proof. reflexivity. Defined.

Lemma hzsign_nattohz m : - nattohz m == natnattohz 0 m. (* move to hz.v *)
Proof. reflexivity. Defined.

Lemma hzsign_hzsign (i:hz) : - - i == i.
Proof. apply (grinvinv ZZ). Defined.

Definition hz_normal_form (i:ZZ) :=
  coprod (total2 (fun n => natnattohz n 0 == i))
         (total2 (fun n => natnattohz 0 (S n) == i)).

Definition hz_to_normal_form (i:ZZ) : hz_normal_form i.
Proof. intros. destruct (hzlthorgeh i 0) as [r|s].
       { apply inr. assert (a := hzabsvallth0 r). assert (b := hzlthtoneq _ _ r).
         assert (c := hzabsvalneq0 b). assert (d := natneq0togth0 _ c).
         assert (f := natgthtogehsn _ _ d). assert (g := minusplusnmm _ _ f).
         rewrite natpluscomm in g. simpl in g. exists (hzabsval i - 1)%nat.
         rewrite g. apply hzinvmaponpathsminus. exact a. }
       { apply inl. exists (hzabsval i). exact (hzabsvalgeh0 s). } Defined.

Lemma nattohz_inj {m n} : nattohz m == nattohz n -> m == n.
Proof. exact (invmaponpathsincl _ isinclnattohz). Defined.

Lemma hzdichot {m n} : neg (nattohz m == - nattohz (S n)).
Proof. intros. intro e. assert (d := ap hzsign e); clear e.
       rewrite hzsign_hzsign in d.
       assert( f := ap (fun i => nattohz m + i) d); simpl in f; clear d.
       change (nattohz m + - nattohz m) with (nattohz m - nattohz m) in f.
       rewrite hzrminus in f. change (0 == nattohz (m + S n)) in f.
       assert (g := nattohz_inj f); clear f. rewrite natpluscomm in g.
       exact (negpaths0sx _ g). Defined.

Definition negpos' : isweq (@pr1 _ hz_normal_form).
Proof. apply isweqpr1; intro i.
       exists (hz_to_normal_form i).
       generalize (hz_to_normal_form i) as s.
       intros [[m p]|[m p]] [[n q]|[n q]].
       { apply (ap (@ii1 (total2 (fun n => natnattohz n 0 == i)) 
                         (total2 (fun n => natnattohz 0 (S n) == i)))).
         apply (proofirrelevance _ (isinclnattohz i)). }
       { apply fromempty. assert (r := p@!q); clear p q. apply (hzdichot r). }
       { apply fromempty. assert (r := q@!p); clear p q. apply (hzdichot r). }
       { apply (ap (@ii2 (total2 (fun n => natnattohz n 0 == i)) 
                         (total2 (fun n => natnattohz 0 (S n) == i)))).
         assert (p' := ap hzsign p). assert (q' := ap hzsign q).
         change (- natnattohz O (S m)) with  (nattohz (S m)) in p'.
         change (- natnattohz O (S n)) with  (nattohz (S n)) in q'.
         assert (c := proofirrelevance _ (isinclnattohz (-i)) (S m,,p') (S n,,q')).
         assert (d := ap pr1 c); simpl in d.
         assert (e := invmaponpathsS _ _ d); clear d.
         apply (pair_path_props (!e)). intro k. apply setproperty. } Defined.

Definition negpos : weq ZZ (coprod nat nat). (* ZZ = (-inf,-1) + (0,inf) *)
Proof. refine (weqpair _ (gradth _ _ _ _)).
       { intro i. destruct (hz_to_normal_form i) as [[n p]|[m q]].
         { exact (inr n). } { exact (inl m). } }
       { intros [n'|n]. 
         { exact (natnattohz 0 (S n')). } { exact (natnattohz n 0). } }
       { simpl. intro i. 
         destruct (hz_to_normal_form i) as [[n p]|[m q]].
         { exact p. } { exact q. } }
       { intros [n'|n].
         { simpl. rewrite natminuseqn. reflexivity. }
         { simpl. rewrite hzabsvalnat. reflexivity. } } Defined.

Definition eta_pair {T} (P:T->Type) (w:total2 P) : 
  tpair P (pr1 w) (pr2 w) == w.
Proof. intros. destruct w. reflexivity. Defined.

Definition eta_weqpair {X Y} (f:weq X Y) : 
  weqpair (pr1 f) (pr2 f) == f.
Proof. intros. apply eta_pair. Defined.

Definition pathpath {X} {w x y z:X} : w==x -> y==z -> (w==y) == (x==z).
Proof. intros ? ? ? ? ? p q.  destruct p,q. reflexivity. Defined.

Definition weqonpaths2 {X Y} (w:weq X Y) {x x':X} {y y':Y} :
  w x == y -> w x' == y' -> weq (x == x') (y == y').
Proof. intros ? ? ? ? ? ? ? p q. destruct p,q. apply weqonpaths. Defined.

Definition eqweqmap_ap {T} (P:T->Type) {t t':T} (e:t==t') (f:sections P) :
  eqweqmap (ap P e) (f t) == f t'. (* move near eqweqmap *)
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmap_ap' {T} (P:T->Type) {t t':T} (e:t==t') (f:sections P) :
  invmap (eqweqmap (ap P e)) (f t') == f t. (* move near eqweqmap *)
Proof. intros. destruct e. reflexivity. Defined.

Lemma hzminusplus (x y:hz) : -(x+y) == (-x) + (-y). (* move to hz.v *)
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

Definition hz_rect (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) : forall i, P i.
Proof. intros.
       destruct (hz_to_normal_form i) as [[n p]|[m q]].
       { exact (p # nat_rect (fun n => P(toZZ n)) p0 IH n). } 
       { exact (q # nat_rect (fun n => P(- toZZ n)) p0 IH' (S m)). }
Defined.

Lemma ZZRecursionUniq (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  iscontr (total2 (ZZRecursionData0 P p0 IH IH')).
Proof. intros.
       unfold ZZRecursionData0.
       (* use hNatRecursionEquiv and negpos' *)
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
       rewrite e in G; clear e. unfold ZZRecursionData in G.
       refine (weqcomp _ G). clear G ih ih' P'.
       refine (weqbandf (weqonsecbase _ w) _ _ _). intro f.
       refine (weqcomp (weqonsecbase _ w) _).
       change (set_to_type (trivialTorsor ZZ)) with (set_to_type ZZ).
       refine (weqcomp (weqonsecbase _ (invweq negpos)) _).
       refine (weqcomp (weqsecovercoprodtoprod _) _).
       refine (weqcomp (weqdirprodcomm _ _) _). apply weqdirprodf.
       { clear k2 l2. apply weqonseqfibers; intro n. simpl.
         unfold invmap, negpos; simpl. unfold right_mult; simpl.
         unfold maponsec1; simpl. refine (weqcomp (weqonpaths (l1 n) _ _) _).
         apply eqweqmap. apply pathpath.
         { unfold l1. rewrite eqweqmap_ap. reflexivity. }
         { reflexivity. } }
       { clear k1 l1. apply weqonseqfibers; intro n. simpl.
         unfold invmap, negpos; simpl. unfold right_mult; simpl.
         unfold maponsec1; simpl. 
         refine (weqcomp (weqpair _ (isweqpathsinv0 _ _)) _).
         refine (weqonpaths2 _ _ _).
         { apply invweq. apply IH. }
         { simpl. rewrite homotinvweqweq. reflexivity. }
         { simpl. apply (ap (invmap (IH _))). rewrite eta_weqpair.
           unfold l2; simpl. rewrite eqweqmap_ap'. reflexivity. } } Defined.

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
