(** * Construction of affine lines *)

Unset Automatic Introduction.
Require Import algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations Nat.
Import pathnotations.PathNotations Utilities.Notation Utilities.NatNotation.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Definition ZZ := hzaddabgr.
Definition toZZ (n:nat) : ZZ := nattohz n.
Definition toZZneg (n:nat) : ZZ := natnattohz O n.
Definition zero := toZZ 0.
Definition one := toZZ 1.

Open Scope hz_scope.

Definition hzabsvalnat n : hzabsval (natnattohz n 0) == n. (* move to hz.v *)
Proof. intros. unfold hzabsval. unfold setquotuniv. simpl.
       unfold hzabsvalint. simpl. destruct (natgthorleh n 0).
       { apply natminuseqn. } { exact (! (natleh0tois0 _ h)). } Defined.

Lemma hzsign_natnattohz m n : - natnattohz m n == natnattohz n m. (* move to hz.v *)
Proof. reflexivity.             (* don't change the proof *)
Defined.

Lemma hzsign_nattohz m : - nattohz m == natnattohz 0 m. (* move to hz.v *)
Proof. reflexivity.             (* don't change the proof *)
Defined.

Lemma hzsign_hzsign (i:hz) : - - i == i.
Proof. apply (grinvinv ZZ). Defined.

Definition hz_normal_form (i:ZZ) :=
  coprod (total2 (fun n => natnattohz n 0 == i))
         (total2 (fun n => natnattohz 0 (S n) == i)).

Definition hznf_pos n := _,, inl (n,,idpath _) : total2 hz_normal_form.

Definition hznf_neg n := _,, inr (n,,idpath _) : total2 hz_normal_form.

Definition hznf_zero := hznf_pos 0.

Definition hznf_neg_one := hznf_neg 0.

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

Definition negpos_weq := weqpair _ negpos' : weq (total2 hz_normal_form) ZZ.

Definition negpos : weq (coprod nat nat) ZZ. (* ZZ = (-inf,-1) + (0,inf) *)
Proof. refine (weqpair _ (gradth _ _ _ _)).
       { intros [n'|n]. 
         { exact (natnattohz 0 (S n')). } { exact (natnattohz n 0). } }
       { intro i. destruct (hz_to_normal_form i) as [[n p]|[m q]].
         { exact (inr n). } { exact (inl m). } }
       { intros [n'|n].
         { simpl. rewrite natminuseqn. reflexivity. }
         { simpl. rewrite hzabsvalnat. reflexivity. } } 
       { simpl. intro i. 
         destruct (hz_to_normal_form i) as [[n p]|[m q]].
         { exact p. } { exact q. } }
Defined.

Definition eta_pair {T} (P:T->Type) (w:total2 P) : 
  tpair P (pr1 w) (pr2 w) == w.
Proof. intros. destruct w. reflexivity. Defined.

Definition eta_weqpair {X Y} (f:weq X Y) : 
  weqpair (pr1 f) (pr2 f) == f.
Proof. intros. apply eta_pair. Defined.

Definition pathpath {X} {w x y z:X} : w==x -> y==z -> (w==y) == (x==z).
Proof. intros ? ? ? ? ? p q.  destruct p,q. reflexivity. Defined.

Definition weqonpaths1 {X} {x x' y y':X} : 
  x == y -> x' == y' -> weq (x == x') (y == y').
Proof. intros ? ? ? ? ? p q. destruct p,q. apply idweq. Defined.

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

Definition dirprod3 X Y Z := dirprod X (dirprod Y Z).

Definition tuple3 {X Y Z} x y z := (x,,(y,,z)) : dirprod3 X Y Z.

Definition paths3 {X Y Z} {x x':X} {y y':Y} {z z':Z} :
  x==x' -> y==y' -> z==z' -> tuple3 x y z == tuple3 x' y' z'. 
Proof. intros ? ? ? ? ? ? ? ? ? p q r. destruct p, q, r. reflexivity.
Defined.       

Definition dirprod4 W X Y Z := dirprod W (dirprod3 X Y Z).

Definition tuple4 {W X Y Z} (w:W) x y z := (w,,tuple3 x y z) : dirprod4 W X Y Z.

Definition paths4 {W X Y Z} {w w':W} {x x':X} {y y':Y} {z z':Z} :
  w==w' -> x==x' -> y==y' -> z==z' -> tuple4 w x y z == tuple4 w' x' y' z'. 
Proof. intros ? ? ? ? ? ? ? ? ? ? ? ? o p q r. destruct o, p, q, r. reflexivity.
Defined.

Definition total3 
           {X} 
           {Y:forall (x:X), Type}
           (Z:forall (x:X) (y:Y x), Type) :=
  total2 (fun x => total2 (Z x)).

Definition total4
           {X} 
           {Y:forall (x:X), Type}
           {Z:forall (x:X) (y:Y x), Type}
           (B:forall (x:X) (y:Y x) (z:Z x y), Type) :=
  total2 (fun x => total3 (B x)).

Definition ZZRecursionData0 (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) := fun 
          f:forall i, P i => dirprod3
            (f zero==p0)
            (forall n, f(  toZZ (S n))==IH  n (f (  toZZ n)))
            (forall n, f(- toZZ (S n))==IH' n (f (- toZZ n))).

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

Definition weq_total2_prod {X Y} (Z:Y->Type) :
  weq (total2 (fun y => dirprod X (Z y))) (dirprod X (total2 Z)).
Proof. intros. refine (weqpair _ (gradth _ _ _ _)).
       { intros [y [x z]]. exact (x,,(y,,z)). }
       { intros [x [y z]]. exact (y,,(x,,z)). }
       { intros [y [x z]]. reflexivity. }
       { intros [x [y z]]. reflexivity. } Defined.

Lemma ZZRecursionUniq (P:ZZ->Type) (p0:P zero) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) :
  iscontr (total2 (ZZRecursionData0 P p0 IH IH')).
Proof. intros.
       unfold ZZRecursionData0.
       (* use hNatRecursionEquiv *)
       apply ( iscontrweqb (Y := total2 (fun f : forall w, P (negpos w) =>
          dirprod4
            (f (ii2 O) == p0)
            (forall n : nat, f (ii2 (S n)) == IH n (f (ii2 n)))
            (f (ii1 O) == IH' O (f (ii2 O)))
            (forall n : nat, f (ii1 (S n)) == IH' (S n) (f (ii1 n)))))).
       { apply (weqbandf (weqonsecbase _ negpos)). intro f.
         refine (weqpair _ (gradth _ _ _ _)).
         { intros [h0 [hp hn]]. refine (tuple4 _ _ _ _). 
           { exact h0. } { exact hp. } 
           { exact (hn O). } { intro n. exact (hn (S n)). } }
         { intros [h0 [hp [h1' hn]]]. refine (tuple3 _ _ _).
           { exact h0. } { exact hp. }
           { intros [|n']. { exact h1'. } { exact (hn n'). } } }
         { intros [h0 [hp hn]]. simpl. apply paths3. 
           { reflexivity. } { reflexivity. }
           { apply funextsec; intros [|n']; reflexivity; reflexivity. } }
         { intros [h0 [h1' [hp hn]]]. reflexivity. } }
       intermediate_iscontr (
         total2 (
             fun f : dirprod (forall n, P (negpos (ii1 n)))
                             (forall n, P (negpos (ii2 n))) =>
              dirprod4
                (pr2 f O == p0)
                (forall n : nat, pr2 f (S n) == IH n (pr2 f n))
                (pr1 f O == IH' O (pr2 f O))
                (forall n : nat, pr1 f (S n) == IH' (S n) (pr1 f n)))).
       { apply (weqbandf (weqsecovercoprodtoprod (fun w => P (negpos w)))). 
         intro f. apply idweq. }
       intermediate_iscontr (
         total2 (
             fun f : dirprod (forall n, P (negpos (ii2 n)))
                             (forall n, P (negpos (ii1 n))) =>
              dirprod4
                (pr1 f O == p0)
                (forall n : nat, pr1 f (S n) == IH n (pr1 f n))
                (pr2 f O == IH' O (pr1 f O))
                (forall n : nat, pr2 f (S n) == IH' (S n) (pr2 f n)))).
       { apply (weqbandf (weqdirprodcomm _ _)). intro f. apply idweq. }
       intermediate_iscontr (
         total2 ( fun 
                f2 : forall n : nat, P (negpos (ii2 n)) => total2 (fun
                f1 : forall n : nat, P (negpos (ii1 n)) => dirprod4
                     (f2 O == p0)
                     (forall n : nat, f2 (S n) == IH n (f2 n))
                     (f1 O == IH' O (f2 O))
                     (forall n : nat, f1 (S n) == IH' (S n) (f1 n))))).
       { apply weqtotal2asstor. }
       intermediate_iscontr (
         total2 ( fun 
            f2 : forall n : nat, P (negpos (ii2 n)) => dirprod
                 (f2 O == p0)
                 (total2 (fun
            f1 : forall n : nat, P (negpos (ii1 n)) => dirprod3
                 (forall n : nat, f2 (S n) == IH n (f2 n))
                 (f1 O == IH' O (f2 O))
                 (forall n : nat, f1 (S n) == IH' (S n) (f1 n)))))).
       { apply weqfibtototal; intro f2. apply weq_total2_prod. }
       intermediate_iscontr (
         total2 ( fun 
            f2 : forall n : nat, P (negpos (ii2 n)) => dirprod3
                 (f2 O == p0)
                 (forall n : nat, f2 (S n) == IH n (f2 n))
                 (total2 (fun
            f1 : forall n : nat, P (negpos (ii1 n)) => dirprod
                 (f1 O == IH' O (f2 O))
                 (forall n : nat, f1 (S n) == IH' (S n) (f1 n)))))).
       { apply weqfibtototal; intro f2. apply weqfibtototal; intro.
         apply weq_total2_prod. }
       intermediate_iscontr (
         total2 ( fun 
            f2 : forall n : nat, P (negpos (ii2 n)) => dirprod
                 (f2 O == p0)
                 (forall n : nat, f2 (S n) == IH n (f2 n)))).
       { apply weqfibtototal; intro f2. apply weqfibtototal; intro h0.
         apply weqpr1; intro ih2. 
         exact (Nat.Uniqueness.hNatRecursionUniq
                   (fun n => P (negpos (ii1 n))) 
                   (IH' O (f2 O))
                   (fun n => IH' (S n))). }
       apply Nat.Uniqueness.hNatRecursionUniq.
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
  weq (total2 (ZZRecursionData P IH IH')) (P 0).
Proof. intros. exists (fun f => pr1 f zero). intro p0.
       apply (iscontrweqf (A _ _ _ _)). apply ZZRecursionUniq. Defined.

Lemma ZZRecursionEquiv_compute (P:ZZ->Type) 
      (IH :forall n, P(  toZZ n) -> P(  toZZ (S n)))
      (IH':forall n, P(- toZZ n) -> P(- toZZ (S n))) 
      (fh : total2 (ZZRecursionData P IH IH')) :
  ZZRecursionEquiv P IH IH' fh == pr1 fh zero.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition ZZBiRecursionData (P:ZZ->Type) (IH :forall i, P(i) -> P(1+i)) := 
  fun f:forall i, P i => forall i, f(1+i)==IH i (f i).

Definition weqonsec {X Y} (P:X->Type) (Q:Y->Type)
           (f:weq X Y) (g:forall x, weq (P x) (Q (f x))) :
  weq (sections P) (sections Q).
Proof. intros.
       exact (weqcomp (weqonsecfibers P (fun x => Q(f x)) g)
                      (invweq (weqonsecbase Q f))). Defined.

Definition weq_transportf {X} (P:X->Type) {x y:X} (p:x==y) : weq (P x) (P y).
Proof. intros. destruct p. apply idweq. Defined.

Definition weq_transportf_comp {X} (P:X->Type) {x y:X} (p:x==y) (f:sections P) :
  weq_transportf P p (f x) == f y.
Proof. intros. destruct p. reflexivity. Defined.

(* the next lemma is needed, perhaps because of an ambiguous coercion *)
Definition change_pr1weq {X Y} (f:weq X Y) : pr1 f == pr1weq _ _ f.
Proof. reflexivity. Defined.

Definition ZZBiRecursionEquiv (P:ZZ->Type) (IH :forall i, weq (P i) (P(1+i))) :
  weq (total2 (ZZBiRecursionData P IH)) (P 0).
Proof. intros.
       assert (k : forall n, one + toZZ n == toZZ (S n)).
       { intro. rewrite nattohzandS. reflexivity. }
       set (l := fun n : nat => weq_transportf P (k n)).
       assert (k' : forall n, - toZZ n == one + (- toZZ (S n))).
       { intros. unfold one, toZZ. rewrite nattohzand1.
         rewrite nattohzandS. rewrite hzminusplus. rewrite <- (hzplusassoc one).
         rewrite (hzpluscomm one). rewrite hzlminus. rewrite hzplusl0.
         reflexivity. }
       set (l' := fun n => weq_transportf P (k' n)).
       set (ih := fun n => weqcomp (IH (toZZ n)) (l n)).
       set (ih':= fun n => (weqcomp (l' n) (invweq (IH (- toZZ (S n)))))).
       set (G := ZZRecursionEquiv P ih ih'). refine (weqcomp _ G).
       apply weqfibtototal. intro f. unfold ZZRecursionData, ZZBiRecursionData.
       refine (weqcomp (weqonsecbase _ negpos) _).
       refine (weqcomp (weqsecovercoprodtoprod _) _).
       refine (weqcomp (weqdirprodcomm _ _) _). apply weqdirprodf.
       { apply weqonsecfibers; intro n. refine (weqonpaths2 _ _ _).
         { change (negpos (ii2 n)) with (toZZ n). exact (l n). }
         { unfold l. apply weq_transportf_comp. }
         { reflexivity. } }
       { apply weqonsecfibers; intro n. simpl.
         refine (weqcomp (weqpair _ (isweqpathsinv0 _ _)) _).
         refine (weqonpaths2 _ _ _).
         { apply invweq. apply IH. }
         { simpl. rewrite homotinvweqweq. reflexivity. }
         { simpl. change (natnattohz 0 (S n)) with (- toZZ (S n)).
           unfold l'. rewrite change_pr1weq. rewrite weq_transportf_comp.
           reflexivity. } } Defined.

Definition ZZBiRecursionEquiv_compute (P:ZZ->Type)
           (IH :forall i, weq (P i) (P(1+i))) 
      (fh : total2 (ZZBiRecursionData P IH)) :
  ZZBiRecursionEquiv P IH fh == pr1 fh 0.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Notation "n + x" := (ac_mult _ n x) : action_scope.
Notation "n - m" := (quotient _ n m) : action_scope.
Open Scope action_scope.

Definition swequiv {X Y} (f:weq X Y) {x y} : y == f x -> invweq f y == x.
Proof. intros ? ? ? ? ? p. exact (ap (invweq f) p @ homotinvweqweq f x). Defined.

Definition swequiv' {X Y} (f:weq X Y) {x y} : invweq f y == x -> y == f x.
Proof. intros ? ? ? ? ? p. exact (! homotweqinvweq f y @ ap f p). Defined.

Definition weqbandfrel {X Y T} 
           (e:Y->T) (t:T) (f : weq X Y) 
           (P:X -> Type) (Q: Y -> Type)
           (g:forall x:X, weq (P x) (Q (f x))) :
  weq (hfiber (fun xp:total2 P => e(f(pr1 xp))) t)
      (hfiber (fun yq:total2 Q => e(  pr1 yq )) t).
Proof. intros. refine (weqbandf (weqbandf f _ _ g) _ _ _).
       intros [x p]. simpl. apply idweq. Defined.

Definition weq_over_sections {S T} (w:weq S T) 
           {s0:S} {t0:T} (k:w s0 == t0)
           {P:T->Type} 
           (p0:P t0) (pw0:P(w s0)) (l:k#pw0 == p0)
           (H:sections P -> Type) 
           (J:sections (funcomp w P) -> Type)
           (g:forall f:sections P, weq (H f) (J (maponsec1 P w f))) :
  weq (hfiber (fun fh:total2 H => pr1 fh t0) p0 )
      (hfiber (fun fh:total2 J => pr1 fh s0) pw0).
Proof. intros. refine (weqbandf _ _ _ _).
       { refine (weqbandf _ _ _ _).
         { exact (weqonsecbase P w). }
         { unfold weqonsecbase; simpl. exact g. } }
       { intros [f h]. simpl. unfold maponsec1; simpl.
         destruct k, l; simpl. unfold transportf; simpl.
         unfold idfun; simpl. apply idweq. } Defined.

Definition transportbfinv {T} (P:T->Type) {t u:T} (e:t==u) (p:P t) : e#'e#p == p.
Proof. intros. destruct e. reflexivity. Defined.

Definition transportfbinv {T} (P:T->Type) {t u:T} (e:t==u) (p:P u) : e#e#'p == p.
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmapap_inv {T} (P:T->Type) {t u:T} (e:t==u) (p:P u) :
  (eqweqmap (ap P e)) ((eqweqmap (ap P (!e))) p) == p.
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmapap_inv' {T} (P:T->Type) {t u:T} (e:t==u) (p:P t) :
  (eqweqmap (ap P (!e))) ((eqweqmap (ap P e)) p) == p.
Proof. intros. destruct e. reflexivity. Defined.

Definition ZZTorsorRecursionEquiv {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t))) :
  forall t0,
  weq (total2 (fun 
          f:forall t, P t => 
            forall t, f (one + t) == IH t (f t)))
      (P t0).
Proof. intros.
       exists (fun fh => pr1 fh t0). intro q.
       set (w := triviality_isomorphism T t0).
       assert (k0 : forall i, one + w i == w (1+i)%hz).
       { intros. simpl. unfold right_mult, ac_mult. rewrite act_assoc.
         reflexivity. }
       set (l0 := (fun i => eqweqmap (ap P (k0 i))) 
               : forall i, weq (P(one + w i)) (P(w(1+i)%hz))).
       assert( e : right_mult t0 zero == t0 ). { apply act_unit. }
       set (H := fun f => forall t : T, f (one + t) == (IH t) (f t)).
       set ( IH' := (fun i => weqcomp (IH (w i)) (l0 i))
                    : forall i:ZZ, weq (P (w i)) (P (w(1+i)%hz))).
       set (J := fun f => forall i : ZZ, f (1 + i)%hz == (IH' i) (f i)).
       refine (iscontrweqb (@weq_over_sections ZZ T w 0 t0 e P q (e#'q) _ H J _) _).
       { apply transportfbinv. }
       { intro. apply invweq. unfold H,J,maponsec1. refine (weqonsec _ _ w _).
         intro i.
         refine (weqonpaths2 _ _ _).
         { exact (invweq (l0 i)). }
         { unfold l0. rewrite (k0 i). reflexivity. }
         { unfold IH'. unfold weqcomp; simpl. 
           change (pr1 (l0 i)) with (pr1weq _ _ (l0 i)). 
           rewrite (homotinvweqweq (l0 i)). reflexivity. } }
       exact (pr2 (ZZBiRecursionEquiv (fun i => P(w i)) IH') (e #' q)).
Defined.

Definition ZZTorsorRecursion_compute {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t:T) :
  forall h, ZZTorsorRecursionEquiv P IH t h == pr1 h t.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition ZZTorsorRecursion_transition {T:Torsor ZZ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t:T) :
  forall h,
  (ZZTorsorRecursionEquiv P IH (one+t) h)
  == 
  IH t (ZZTorsorRecursionEquiv P IH t h).
Proof. intros. rewrite 2!ZZTorsorRecursion_compute. exact (pr2 h t). Defined.

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

Definition weq_pathscomp0r {X} x {y z:X} (p:y==z) : weq (x==y) (x==z).
Proof. intros. exact (weqpair _ (isweqpathscomp0r _ p)). Defined.

Lemma iscontrGuidedHomotopy {Y} {T:Torsor ZZ} (f:T->Y) (s:target_paths f) :
  iscontr (GuidedHomotopy f s).
Proof. intros. apply (squash_to_prop (torsor_nonempty T)).
       { apply isapropiscontr. }
       intro t0. apply ( iscontrweqb (Y := total2 (fun y => y == f t0))).
       { apply weqfibtototal; intro y.
         exact (ZZTorsorRecursionEquiv _ (fun t => weq_pathscomp0r _ _) t0). }
       apply iscontrcoconustot. Defined.

Definition makeGuidedHomotopy {T:Torsor ZZ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y==f t0) : 
  GuidedHomotopy f s.
Proof. intros. exact (y ,, invweq (ZZTorsorRecursionEquiv 
               (fun t : T => y == f t)
               (fun t => weq_pathscomp0r y (s t))
               t0) h0). Defined.

Definition makeGuidedHomotopy_path {T:Torsor ZZ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y==f t0)
           {y':Y} (p:y'==y) :
  makeGuidedHomotopy f s t0 (p@h0) == makeGuidedHomotopy f s t0 h0.
Proof. intros. apply (total2_paths2 p). destruct p. reflexivity. Defined.

Definition makeGuidedHomotopy_path' {T:Torsor ZZ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y==f t0) :
  makeGuidedHomotopy f s t0 h0 == makeGuidedHomotopy f s (one+t0) (h0 @ s t0).
Proof. intros. 
       admit.
Defined.

Definition affine_line (T:Torsor ZZ) := squash T.

Lemma iscontr_affine_line (T:Torsor ZZ) : iscontr (affine_line T).
Proof. intros. apply iscontraprop1. { apply isaprop_squash. }
       exact (torsor_nonempty T). Defined.

Definition map {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) : 
  affine_line T -> GuidedHomotopy f s.
Proof. intros ? ? ? ? t'. 
       (* try to use transport as in Halfline.map *)
       apply (squash_to_prop t').
       { apply isapropifcontr. apply iscontrGuidedHomotopy. }
       intro t; clear t'.
       exact (makeGuidedHomotopy f s t (idpath _)). Defined.

Definition affine_line_map {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) : 
  affine_line T -> Y.
Proof. intros ? ? ? ? t'. exact (pr1 (map f s t')). Defined.

Definition check_values {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) t :
  affine_line_map f s (squash_element t) == f t.
Proof. intros. unfold affine_line_map, map, squash_element, squash_to_prop.
       simpl. reflexivity. Defined.

Definition map_path {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) : 
  forall t, map f s (squash_element t) == map f s (squash_element (one + t)).
Proof. intros. refine (total2_paths2 _ _). 
       { exact (s t). }
       { simpl.
         (* Set Printing All.  *)
         Unset Printing Notations.
         simpl.

         
         
         admit. }
Defined.

Definition map_path_check {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) :
  forall t, forall p : map f s (squash_element t) ==
                       map f s (squash_element (one + t)),
    ap pr1 p == s t.
Proof. intros. set (q := map_path f s t). assert (k : q==p). 
       { apply (hlevelntosn 1); apply (hlevelntosn 0). 
         apply iscontrGuidedHomotopy. }
       destruct k. apply total2_paths2_comp1. Defined.

Definition check_paths {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) (t:T) :
  ap (affine_line_map f s) (squash_path t (one + t)) == s t.
Proof. intros. refine (_ @ map_path_check f s t _).
       apply pathsinv0. apply maponpathscomp. Defined.

Definition affine_line_value {T:Torsor ZZ} {Y} (f:T->Y) (s:target_paths f) : Y.
Proof. intros. exact (affine_line_map f s (torsor_nonempty T)). Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/AffineLine.vo"
End:
*)
