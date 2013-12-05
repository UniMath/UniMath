(** * experimental file concerning eta reduction *)

Require Import Ktheory.Utilities.
Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.pathnotations.
Require Import Ktheory.Utilities.
        Import RezkCompletion.pathnotations.PathNotations.
        Import Ktheory.Utilities.Notations.
Unset Automatic Introduction.

(** * trivial path lemmas, perhaps not needed *)

Lemma funcomppathl {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : funcomp f g == funcomp f g'.
Proof. intros. exact (ap (funcomp f) e). Defined.

Lemma funcomppathr {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : funcomp f g == funcomp f' g.
Proof. intros. exact (ap (fun f => funcomp f g) e).  Defined.

Lemma funcomppathlfunctor {W X Y Z:UU} (b:W->X) (f:X->Y) {g g':Y->Z} (e:g==g') :
  funcomppathl b (funcomppathl f e) == funcomppathl (funcomp b f) e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathcomp {X Y Z:UU} (f:X->Y) {g g' g'':Y->Z} (e:g==g') (e':g'==g'') :
  funcomppathl f e @ funcomppathl f e' == funcomppathl f (e @ e').
Proof. destruct e. trivial. Defined.

Lemma funcomppathlpathrev {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : 
  funcomppathl f (!e) == !funcomppathl f e.
Proof. destruct e. trivial. Defined.

Lemma funcomppathrfunctor {X Y Z W:UU} {f f':X->Y} (e:f==f') (g:Y->Z) (f0:Z->W) :
  funcomppathr (funcomppathr e g) f0 == funcomppathr e (funcomp g f0).
Proof. destruct e. trivial. Defined.

Lemma funcomppathrpathcomp {X Y Z:UU} {f f' f'':X->Y} (e:f==f') (e':f'==f'') (g:Y->Z) : 
  funcomppathr e g @ funcomppathr e' g == funcomppathr (e @ e') g.
Proof. destruct e. trivial. Defined.

Lemma funcomppathrpathrev {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : 
  funcomppathr (!e) g == ! funcomppathr e g.
Proof. destruct e. trivial. Defined.

Lemma funcomppaths {X Y Z:UU} {f f':X->Y} {g g':Y->Z} (p:f==f') (q:g==g') : funcomp f g == funcomp f' g'.
Proof. intros. destruct p, q. trivial. Defined.

Lemma funcomppathsquare {X:UU} {f g f0 k : X->X} (p : f==g) (q : f0==k) :
  funcomppathl f q @ funcomppathr p k == funcomppathr p f0 @ funcomppathl g q.
Proof. destruct p, q. trivial. Defined.

(** * eta correction *)

Definition etaExpand {T:UU} (P:T->UU) (f:sections P) := fun t => f t.

Definition etaExpand2 {T U:UU} (V: T -> U -> UU) (f: forall t u, V t u) := fun t u => f t u.

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

Definition etacorrectiontype (T:UU) (P:T -> UU) := idfun (sections P) == etaExpand P.

Axiom etacorrectionfun: forall T P, etacorrectiontype T P.

Lemma etacorrectionfun': forall T P, etacorrectiontype T P.
Proof.
  intros.
  apply funextsec; intro f.
  apply funextsec; intro t.
  apply idpath.
Defined.

(** the following lemma is the same as the axiom etacorrection in uu0.v *)
Lemma etacorrection_follows : 
  forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths f (fun t:T => f t). 
Proof.
  intros.
  exact (ap (evalat f) (etacorrectionfun T P)).
Defined.

Axiom etaright : 
  forall T:UU, forall P:T -> UU, 
    funcomppathr (etacorrectionfun _ _) (etaExpand P) == idpath (etaExpand P).

Lemma etaright' : 
  forall T:UU, forall P:T -> UU, 
    funcomppathr (etacorrectionfun _ _) (etaExpand P) == idpath (etaExpand P).
Proof.
  intros.
  (* try to prove it from functional extensionality *)
  admit.
Defined.

Axiom etaleft :
  forall T:UU, forall P:T -> UU, 
    funcomppathl (etaExpand P) (etacorrectionfun _ _) == idpath (etaExpand P).

Definition mapon2paths { T U : UU } ( f : T -> U ) { t t' : T } { e e': t == t' } ( p : e == e') : 
  ap f e == ap f e'.
Proof. intros .  exact (ap (ap f) p). Defined. 

Lemma etacorrectionrule (T:UU) (P:T -> UU) (f:sections P) :
    etacorrection_follows _ _ (etaExpand _ f) == idpath _.
Proof.                           
  intros.
  exact (  (! maponpathscomp (funcomp (etaExpand _)) (evalat f) (etacorrectionfun _ _))
         @ (mapon2paths (evalat f) (etaleft _ _))).
Defined.

Lemma etacorrectionrule' (T:UU) (P:T -> UU) (f:sections P) :
    ap (etaExpand P) (etacorrection_follows _ _ f) == idpath (etaExpand _ f).
Proof.
  intros.
  exact ( (maponpathscomp (evalat f) (etaExpand P) (etacorrectionfun _ _))
      @   (! maponpathscomp (funcomp' (etaExpand P)) (evalat f) (etacorrectionfun _ _))
      @   (mapon2paths (evalat f) (etaright _ _))).
Defined.

Lemma etacorrectionvalue (T:UU) (P:T -> UU) (f:sections P) (t:T):
    ap (evalsecat t) (etacorrection_follows _ _ f) == idpath (f t).
Proof.
  intros.
  exact (    (! maponpathscomp (etaExpand P) (evalsecat t) (etacorrection_follows _ _ f))
           @ (mapon2paths (evalsecat t) (etacorrectionrule' T P f))).
Defined.

Lemma etacorrection2 (T U:UU) (V: T -> U -> UU) (f: forall t u, V t u) : f == etaExpand2 _ f. 
Proof.
  intros.
  intermediate (etaExpand _ f).
  apply etacorrection_follows.
  apply funextsec.
  intro.
  apply etacorrection_follows.
Defined.

Lemma etacor2 {X Y Z:UU} (f : X -> Y -> Z) : f == fun x y => f x y.
Proof.
  intros.
  apply etacorrection2.
Defined.

Lemma bar : forall (T:UU) (P:T -> UU) (e : idfun (sections P) == etaExpand P), funcomppathr e (etaExpand P) == funcomppathl (etaExpand P) e.
Proof. destruct e. trivial. Defined.

Definition etatype := forall T P,
  total2 (
      fun e : etacorrectiontype T P => 
          dirprod
                (funcomppathr e (etaExpand P) == idpath (etaExpand P))
                (funcomppathl (etaExpand P) e == idpath (etaExpand P))).

Definition threeaxioms := 
  (fun _ _ => etacorrectionfun _ _ ,, etaright _ _ ,, etaleft _ _) : etatype.

Lemma fixetatype : (forall T P, etacorrectiontype T P) -> etatype.
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
Proof. intros. apply (ap (fun k => k f) (pr1 (eta _ _))). Defined.

Lemma funcompidl {X Y:UU} (f:X->Y) (eta:etatype) : f == funcomp (idfun X) f.
Proof. intros. apply etaExpansion. assumption. Defined.

Lemma funcompidl' {X Y:UU} (f:X->Y) : etaExpand _ f == funcomp (idfun X) f.
Proof. trivial. Defined.

Lemma funcompidr {X Y:UU} (f:X->Y) (eta:etatype) : f == funcomp f (idfun Y).
Proof. intros. apply etaExpansion. assumption. Defined.

Lemma funcompidr' {X Y:UU} (f:X->Y) : etaExpand _ f == funcomp f (idfun Y).
Proof. trivial. Defined.

Lemma funcompidlpath {X Y:UU} {f f':X->Y} (p:f==f') : ap (etaExpand _) p == funcomppathl (idfun X) p.
Proof. trivial. Defined.

Lemma funcompidrpath {X Y:UU} {f f':X->Y} (p:f==f') : ap (etaExpand _) p == funcomppathr p (idfun Y).
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
