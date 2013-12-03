(** * experimental file concerning eta reduction *)

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import Foundations.hlevel2.hSet.
Unset Automatic Introduction.

(** * eta correction *)

Definition sections {T:UU} (P:T->UU) := forall t:T, P t.

Definition etaExpand {T:UU} (P:T->UU) (f:sections P) := fun t => f t.

Goal forall (T:UU) (P:T->UU) (f:sections P), etaExpand _ (etaExpand _ f) == etaExpand _ f.
Proof.
  (* just to demonstrate this judgmental equality *)
  intros; exact (idpath _).
Defined.

Goal forall (T:UU) (P:T->UU), funcomp (etaExpand P) (etaExpand P) == etaExpand P.
Proof.
  (* just to demonstrate this judgmental equality *)
  intros; exact (idpath _).
Defined.

Lemma funcomppathl {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : funcomp f g == funcomp f g'.
Proof. intros. destruct e. trivial. Defined.

Lemma funcomppathlfunctor {W X Y Z:UU} (b:W->X) (f:X->Y) {g g':Y->Z} (e:g==g') :
  funcomppathl b (funcomppathl f e) == funcomppathl (funcomp b f) e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathcomp {X Y Z:UU} (f:X->Y) {g g' g'':Y->Z} (e:g==g') (e':g'==g'') :
  funcomppathl f e @ funcomppathl f e' == funcomppathl f (e @ e').
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathrev {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : 
  funcomppathl f (!e) == !funcomppathl f e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathr {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : funcomp f g == funcomp f' g.
Proof. intros. destruct e. trivial. Defined.

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

Lemma funcomppathsquare {X:UU} {f g h k : X->X} (p : f==g) (q : h==k) :
  funcomppathl f q @ funcomppathr p k == funcomppathr p h @ funcomppathl g q.
Proof. destruct p, q. trivial. Defined.

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

Lemma isaprop_wma_inhab (X:UU) : (X -> isaprop X) -> isaprop X.
Proof.
  intros ? f.
  apply invproofirrelevance.
  intros x y.
  apply (f x).
Defined.

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
