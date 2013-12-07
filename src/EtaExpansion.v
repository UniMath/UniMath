(** * experimental file concerning eta reduction *)

Require Import Ktheory.Utilities.
Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.pathnotations.
Require Import Ktheory.Utilities.
        Import RezkCompletion.pathnotations.PathNotations.
        Import Ktheory.Utilities.Notations.
Unset Automatic Introduction.

(** * trivial path lemmas, perhaps not needed *)

Lemma function_then_path {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : funcomp f g == funcomp f g'.
Proof. intros. exact (ap (funcomp f) e). Defined.

Lemma path_then_function {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : funcomp f g == funcomp f' g.
Proof. intros. exact (ap (fun f => funcomp f g) e).  Defined.

Lemma function_then_pathfunctor {W X Y Z:UU} (b:W->X) (f:X->Y) {g g':Y->Z} (e:g==g') :
  function_then_path b (function_then_path f e) == function_then_path (funcomp b f) e.
Proof. destruct e. trivial. Defined.

Lemma function_then_pathpathcomp {X Y Z:UU} (f:X->Y) {g g' g'':Y->Z} (e:g==g') (e':g'==g'') :
  function_then_path f e @ function_then_path f e' == function_then_path f (e @ e').
Proof. destruct e. trivial. Defined.

Lemma function_then_pathpathrev {X Y Z:UU} (f:X->Y) {g g':Y->Z} (e:g==g') : 
  function_then_path f (!e) == !function_then_path f e.
Proof. destruct e. trivial. Defined.

Lemma path_then_functionfunctor {X Y Z W:UU} {f f':X->Y} (e:f==f') (g:Y->Z) (f0:Z->W) :
  path_then_function (path_then_function e g) f0 == path_then_function e (funcomp g f0).
Proof. destruct e. trivial. Defined.

Lemma path_then_functionpathcomp {X Y Z:UU} {f f' f'':X->Y} (e:f==f') (e':f'==f'') (g:Y->Z) : 
  path_then_function e g @ path_then_function e' g == path_then_function (e @ e') g.
Proof. destruct e. trivial. Defined.

Lemma path_then_functionpathrev {X Y Z:UU} {f f':X->Y} (e:f==f') (g:Y->Z) : 
  path_then_function (!e) g == ! path_then_function e g.
Proof. destruct e. trivial. Defined.

Lemma funcomppathsquare {X:UU} {f g f0 k : X->X} (p : f==g) (q : f0==k) :
  function_then_path f q @ path_then_function p k == path_then_function p f0 @ function_then_path g q.
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
    exact ((! path_then_function p (etaExpand P)) @ p).
  clear C p.
  exists (tpair (isleftinverse (etaExpand P)) (idfun _) q).
  intros [C p].
  unfold isleftinverse in p.
  (* Check (! function_then_path C q @ p : etaExpand _ C == (idfun (sections P))). *)
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
Lemma etacorrection_follows {T:UU} {P:T -> UU} (f: sections P): f == fun t:T => f t.
Proof.
  intros.
  exact (ap (evalat f) (etacorrectionfun T P)).
Defined.

Lemma etacor1 {X Y:UU} (f : X -> Y) : f == fun x => f x.
Proof.
  intros.
  apply etacorrection_follows.
Defined.

Axiom etaright : 
  forall T:UU, forall P:T -> UU, 
    path_then_function (etacorrectionfun _ _) (etaExpand P) == idpath (etaExpand P).

Lemma funextfunpath (X Y:UU) (f g:X->Y) (p q:f==g) :
  (forall x:X, ap (evalat x) p == ap (evalat x) q) -> p == q.
Proof.
  intros ? ? ? ? ? ? e.
  apply (invmaponpathsweq (
             (fun (k : f == g) x => ap (evalat x) k) 
               ,,
             (isweqtoforallpaths _ f g))).
  apply funextsec; intro x.
  exact (e x).
Defined.

Lemma funextsecpath (X:UU) (P:X->UU) (f g:sections P) (p q:f==g) :
  (forall x:X, ap (evalsecat x) p == ap (evalsecat x) q) -> p == q.
Proof.
  (* the proof will be similar to that of funextfunpath *)
  admit.
Defined.

Lemma funextsec_compute { T : UU } (P: T-> UU) (f : sections P) (t:T) :
  idpath _
  == 
  ap (evalsecat t) (funextsec P f (etaExpand P f) (fun t => idpath (f t))).
  (* this is a warm-up for the lemma below *)
Proof.
  intros ? ? f t.
  unfold funextsec.
  intermediate (idpath (f t)).  (* cosmetic *)
    apply idpath.
  admit.
Defined.

Lemma etaright' : 
  forall T:UU, forall P:T -> UU, 
    path_then_function (etacorrectionfun' _ _) (etaExpand P) == idpath (etaExpand P).
Proof.
  intros.
  (* try to prove it from functional extensionality *)
  apply funextfunpath; intro g.
  apply funextsecpath; intro t.
  intermediate (idpath (g t)). (* cosmetic *)
    unfold path_then_function.
    unfold etacorrectionfun'.
    (* Check (funextsec_compute P g t). *)
    admit.
  apply idpath.
Defined.

Lemma lefteqright : forall (T:UU) (P:T -> UU) (e : idfun (sections P) == etaExpand P), function_then_path (etaExpand P) e == path_then_function e (etaExpand P).
Proof. destruct e. trivial. Defined.

Axiom etaleft :
  forall T:UU, forall P:T -> UU, 
    function_then_path (etaExpand P) (etacorrectionfun _ _) == idpath (etaExpand P).

Lemma etaleft' :
  forall T:UU, forall P:T -> UU, 
    function_then_path (etaExpand P) (etacorrectionfun' _ _) == idpath (etaExpand P).
Proof.
  intros.
  intermediate (path_then_function (etacorrectionfun' _ _) (etaExpand P)).
    apply lefteqright.
  apply etaright'.
Defined.

Definition mapon2paths { T U : UU } ( f : T -> U ) { t t' : T } { e e': t == t' } ( p : e == e') : 
  ap f e == ap f e'.
Proof. intros .  exact (ap (ap f) p). Defined. 

Lemma etacorrectionrule (T:UU) (P:T -> UU) (f:sections P) :
    etacorrection_follows (etaExpand _ f) == idpath _.
Proof.                           
  intros.
  exact (  (! maponpathscomp (funcomp (etaExpand _)) (evalat f) (etacorrectionfun _ _))
         @ (mapon2paths (evalat f) (etaleft _ _))).
Defined.

Lemma etacorrectionrule' (T:UU) (P:T -> UU) (f:sections P) :
    ap (etaExpand P) (etacorrection_follows f) == idpath (etaExpand _ f).
Proof.
  intros.
  exact ( (maponpathscomp (evalat f) (etaExpand P) (etacorrectionfun _ _))
      @   (! maponpathscomp (funcomp' (etaExpand P)) (evalat f) (etacorrectionfun _ _))
      @   (mapon2paths (evalat f) (etaright _ _))).
Defined.

Lemma etacorrectionvalue (T:UU) (P:T -> UU) (f:sections P) (t:T):
    ap (evalsecat t) (etacorrection_follows f) == idpath (f t).
Proof.
  intros.
  exact (    (! maponpathscomp (etaExpand P) (evalsecat t) (etacorrection_follows f))
           @ (mapon2paths (evalsecat t) (etacorrectionrule' T P f))).
Defined.

Lemma etacorrection2 {T U:UU} {V: T -> U -> UU} (f: forall t u, V t u) : f == etaExpand2 _ f. 
Proof.
  intros.
  apply funextsec; intro t.
  apply funextsec; intro u.
  apply idpath.
Defined.

Definition etatype := forall T P,
  total2 ( fun ecor : etacorrectiontype T P => 
                   path_then_function ecor (etaExpand P) == idpath (etaExpand P)).

Definition twoaxioms := 
  (fun _ _ => etacorrectionfun _ _ ,, etaright _ _) : etatype.

Lemma fixetatype : (forall T P, etacorrectiontype T P) -> etatype.
Proof.
  intros e T P.
  set (eta := e T P).
  exists ( eta @ !(path_then_function eta (etaExpand P)) ).
  assert (p : path_then_function (path_then_function eta (etaExpand P)) (etaExpand P)
           == path_then_function eta (etaExpand P)).
  apply path_then_functionfunctor.
  rewrite <- path_then_functionpathcomp.    
  rewrite path_then_functionpathrev.    
  rewrite p.
  apply pathsinv0r.
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

Lemma funcompidlpath {X Y:UU} {f f':X->Y} (p:f==f') : ap (etaExpand _) p == function_then_path (idfun X) p.
Proof. trivial. Defined.

Lemma funcompidrpath {X Y:UU} {f f':X->Y} (p:f==f') : ap (etaExpand _) p == path_then_function p (idfun Y).
Proof. trivial. Defined.

Lemma isaprop_etatype : isaprop etatype.
  apply impred; intro T.
  apply impred; intro P.
  apply invproofirrelevance.
  intros [eta u] [eta' u'].
  unfold etacorrectiontype in *.
  assert( eta == eta' ).
    apply funextfunpath; intro f.
    apply funextsecpath; intro x.
    Check (ap (ap (evalsecat x)) (ap (ap (evalat f)) u)).
    admit.
  admit.
Qed.

Axiom eta : etatype.
