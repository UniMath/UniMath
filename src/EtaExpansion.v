(** * experimental file concerning eta reduction *)

Require Import Ktheory.Utilities.
Require Import RezkCompletion.pathnotations.
Require Import Foundations.hlevel2.hSet.
Unset Automatic Introduction.
Require Import Ktheory.Utilities.
Import RezkCompletion.pathnotations.PathNotations.

(** * trivial path lemmas, perhaps not needed *)

Lemma funcomppathl {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : funcomp f g == funcomp f g'.
Proof. intros. exact (maponpaths (funcomp f) e). Defined.

Lemma funcomppathr {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : funcomp f g == funcomp f' g.
Proof. intros. exact (maponpaths (fun f => funcomp f g) e).  Defined.

Lemma funcomppathlfunctor {W X Y Z:UU} (b:W->X) (f:X->Y) {g g':Y->Z} (e:g==g') :
  funcomppathl b (funcomppathl f e) == funcomppathl (funcomp b f) e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathcomp {X Y Z:UU} (f:X->Y) {g g' g'':Y->Z} (e:g==g') (e':g'==g'') :
  funcomppathl f e @ funcomppathl f e' == funcomppathl f (e @ e').
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathrev {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : 
  funcomppathl f (!e) == !funcomppathl f e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathrfunctor {X Y Z W:UU} {f f':X->Y} (e:f==f') (g:Y->Z) (h:Z->W) :
  funcomppathr (funcomppathr e g) h == funcomppathr e (funcomp g h).
Proof. destruct e. trivial. Defined.

Lemma funcomppathrpathcomp {X Y Z:UU} {f f' f'':X->Y} (e:f==f') (e':f'==f'') (g:Y->Z) : 
  funcomppathr e g @ funcomppathr e' g == funcomppathr (e @ e') g.
Proof. destruct e. trivial. Defined.

Lemma funcomppathrpathrev {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : 
  funcomppathr (!e) g == ! funcomppathr e g.
Proof. destruct e. trivial. Defined.

Lemma funcomppaths {X Y Z:UU} {f f':X->Y} {g g':Y->Z} (p:f==f') (q:g==g') : funcomp f g == funcomp f' g'.
Proof. intros. destruct p, q. trivial. Defined.

Lemma funcomppathsquare {X:UU} {f g h k : X->X} (p : f==g) (q : h==k) :
  funcomppathl f q @ funcomppathr p k == funcomppathr p h @ funcomppathl g q.
Proof. destruct p, q. trivial. Defined.

(** * eta correction *)

Definition etaExpand {T:UU} (P:T->UU) (f:sections P) := fun t => f t.

Goal forall (T:UU) (P:T->UU), funcomp (etaExpand P) (etaExpand P) == etaExpand P.
Proof.
  (* just to demonstrate this judgmental equality *)
  intros; exact (idpath _).
Defined.

Definition isleftinverse {X:UU} (f:X->X) (g:X->X) := funcomp g f == idfun X.

Definition hasleftinverse {X:UU} (f:X->X) := total2 (isleftinverse f).

Definition etaExpandHasLeftInverse {T:UU} (P:T->UU) := hasleftinverse (etaExpand P).

Lemma isaprop_etaExpandHasLeftInverse {T:UU} (P:T->UU) :
  isaprop (etaExpandHasLeftInverse P).
Proof.
  intros.
  apply isaprop_wma_inhab'.
  intros [C p].
  assert (q : etaExpand P == idfun _).
    exact ((! funcomppathr p (etaExpand P)) @ p).
  clear C p.
  exists (tpair (isleftinverse (etaExpand P)) (idfun _) q).
  intros [C p].
  unfold isleftinverse in p.
  Check (! funcomppathl C q @ p : etaExpand _ C == (idfun (sections P))).
  (* almost ... *)

  admit.
Qed.

Axiom etacorrectionfun: forall T:UU, forall P:T -> UU, idfun (sections P) == etaExpand P.

(** the following lemma is the same as the axiom etacorrection in uu0.v *)
Lemma etacorrection_follows : 
  forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths f (fun t:T => f t). 
Proof.
  intros.
  exact (maponpaths (evalat f) (etacorrectionfun T P)).
Defined.

Axiom etaright : 
  forall T:UU, forall P:T -> UU, 
    funcomppathr (etacorrectionfun _ _) (etaExpand P) == idpath (etaExpand P).

Axiom etaleft :
  forall T:UU, forall P:T -> UU, 
    funcomppathl (etaExpand P) (etacorrectionfun _ _) == idpath (etaExpand P).

Definition mapon2paths { T U : UU } ( f : T -> U ) { t t' : T } { e e': t == t' } ( p : e == e') : 
  maponpaths f e == maponpaths f e'.
Proof. intros .  exact (maponpaths (maponpaths f) p). Defined. 

Lemma etacorrectionrule (T:UU) (P:T -> UU) (f:sections P) :
    etacorrection_follows _ _ (etaExpand _ f) == idpath _.
Proof.                           
  intros.
  intermediate (maponpaths (evalat f) (funcomppathl (etaExpand P) (etacorrectionfun T P))).
    unfold etacorrection_follows, funcomppathl.
    exact (! maponpathscomp (funcomp (etaExpand P)) (evalat f) (etacorrectionfun T P)).
  intermediate (maponpaths (evalat f) (idpath (etaExpand P))).
    exact (mapon2paths (evalat f) (etaleft T P)).
  apply idpath.
Defined.

Lemma etacorrectionrule' (T:UU) (P:T -> UU) (f:sections P) :
    maponpaths (etaExpand P) (etacorrection_follows _ _ f) == idpath (etaExpand _ f).
Proof.
  intros.
  admit.
Defined.

Lemma etacorrectionvalue (T:UU) (P:T -> UU) (f:sections P) (t:T):
    maponpaths (evalsecat t) (etacorrection_follows _ _ f) == idpath (f t).
Proof.
  intros.
  intermediate (maponpaths (evalsecat t) (maponpaths (etaExpand P) (etacorrection_follows _ _ f))).
    exact (! maponpathscomp (etaExpand P) (evalsecat t) (etacorrection_follows _ _ f)).
  intermediate (maponpaths (@evalsecat T P t) (idpath (etaExpand _ f))).
    destruct (etacorrectionrule' T P f).
    apply idpath.
  apply idpath.
Defined.

Lemma etacorrection2: 
  forall (T:UU) (U:UU) (V: T -> U -> UU) (f: (forall (t:T) (u:U), V t u)), 
    f == (fun t u => f t u). 
Proof.
  intros.
  intermediate (etaExpand _ f).
  apply etacorrection_follows.
  apply funextsec.
  intro.
  apply etacorrection_follows.
Defined.

Lemma etacor2 {X Y Z:UU} (f : X -> Y -> Z) : f == fun x y => f x y.
  intros.
  apply etacorrection2.
Defined.

Lemma bar : forall (T:UU) (P:T -> UU) (e : idfun (sections P) == etaExpand P), funcomppathr e (etaExpand P) == funcomppathl (etaExpand P) e.
Proof. destruct e. trivial. Defined.

Definition etatype := forall (T:UU) (P:T -> UU),
  total2 (
      fun e : idfun (sections P) == etaExpand P => 
          dirprod
                (funcomppathr e (etaExpand P) == idpath (etaExpand P))
                (funcomppathl (etaExpand P) e == idpath (etaExpand P))).

Lemma fixetatype : (forall (T:UU) (P:T -> UU), idfun (sections P) == etaExpand P) -> etatype.
Proof.
  intros e T P.
  exists ( e T P @ !(funcomppathr (e T P) (etaExpand P)) ).
  set (eta := e T P).
  split.
    assert (p : funcomppathr (funcomppathr eta (etaExpand P)) (etaExpand P) == funcomppathr eta (etaExpand P)).
      apply funcomppathrfunctor.
    rewrite <- funcomppathrpathcomp.    
    rewrite funcomppathrpathrev.    
    rewrite p.
    apply pathsinv0r.
  (* other half *)
    assert (p : funcomppathl (etaExpand P) (funcomppathl (etaExpand P) eta) == funcomppathl (etaExpand P) eta).
      apply funcomppathlfunctor.
    rewrite <- funcomppathlpathcomp.
    rewrite funcomppathlpathrev.    
    rewrite bar.
    (* rewrite p (* should have worked here, since it worked above *) *)
    assert (foofoo : forall (X:UU) (x y:X) (q q':x==y) (t:q == q'), q' @ !q == idpath _).
      intros. destruct q, t. trivial.
    apply foofoo.
    exact p.
Qed.

Lemma etaExpansion : forall (T:UU) (P:T -> UU) (f:sections P) (eta:etatype), f == etaExpand P f.
Proof. intros. apply (maponpaths (fun k => k f) (pr1 (eta _ _))). Defined.

Lemma funcompidl {X Y:UU} (f:X->Y) (eta:etatype) : f == funcomp (idfun X) f.
Proof. intros. apply etaExpansion. assumption. Defined.

Lemma funcompidl' {X Y:UU} (f:X->Y) : etaExpand _ f == funcomp (idfun X) f.
Proof. trivial. Defined.

Lemma funcompidr {X Y:UU} (f:X->Y) (eta:etatype) : f == funcomp f (idfun Y).
Proof. intros. apply etaExpansion. assumption. Defined.

Lemma funcompidr' {X Y:UU} (f:X->Y) : etaExpand _ f == funcomp f (idfun Y).
Proof. trivial. Defined.

Lemma funcompidlpath {X Y:UU} {f f':X->Y} (p:f==f') : maponpaths (etaExpand _) p == funcomppathl (idfun X) p.
Proof. trivial. Defined.

Lemma funcompidrpath {X Y:UU} {f f':X->Y} (p:f==f') : maponpaths (etaExpand _) p == funcomppathr p (idfun Y).
Proof. trivial. Defined.

Lemma isaprop_etatype : isaprop (etatype).
Proof.
  apply isaprop_wma_inhab; intro eta0.
  apply impred; intro T.
  apply impred; intro P.
  apply invproofirrelevance.
  intros [eta [u v]] [eta' [u' v']].
  assert (m : paths
        (funcomppathl (idfun (sections P)) eta' @ funcomppathr eta (etaExpand P))
        (funcomppathr eta (idfun (sections P)) @ funcomppathl (etaExpand P) eta')).
    exact (funcomppathsquare eta eta').
  rewrite u, v', pathscomp0rid, pathscomp0rid in m.
  rewrite <- funcompidrpath, <- funcompidlpath in m.
  
  assert( t : funcomppathl (idfun (sections P)) eta' == eta' ).
    
  admit. admit.
Qed.

Axiom eta : etatype.
