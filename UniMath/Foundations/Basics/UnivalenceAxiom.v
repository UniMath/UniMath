(** * Univalence axiom and functional extensionality.  Vladimir Voevodsky. Feb. 2010 - Sep. 2011

This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun.

*)

(** Preliminaries  *)

Require Export UniMath.Foundations.Basics.PartB.

(* everything related to eta correction is obsolete *)

Definition etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths f (fun t:T => f t).
Proof. reflexivity. Defined.

Lemma isweqetacorrection { T : UU } (P:T -> UU): isweq (fun f: forall t:T, P t => (fun t:T => f t)).
Proof. intros. apply idisweq. Defined.

Definition weqeta { T : UU } (P:T -> UU) := weqpair _ ( isweqetacorrection P ) .

Lemma etacorrectiononpaths { T : UU } (P:T->UU)(s1 s2 :forall t:T, P t) : paths (fun t:T => s1 t) (fun t:T => s2 t)-> paths s1 s2.
Proof. intros X. set (ew := weqeta P). apply (invmaponpathsweq ew s1 s2 X). Defined.

Definition etacor { X Y : UU } (f:X -> Y) : paths f (fun x:X => f x) := etacorrection _ (fun T:X => Y) f.

Lemma etacoronpaths { X Y : UU } (f1 f2 : X->Y) : paths (fun x:X => f1 x) (fun x:X => f2 x) -> paths f1 f2.
Proof. intros X0. set (ec:= weqeta (fun x:X => Y) ). apply (invmaponpathsweq  ec f1 f2 X0). Defined.

Definition eqweqmap { T1 T2 : UU } : T1 = T2 -> T1 ≃ T2.
Proof. intro e. induction e. apply idweq. Defined.

Definition toforallpaths { T : UU } (P:T -> UU) (f g :forall t:T, P t) : f = g -> f ~ g.
Proof. intros h t. induction h.  apply (idpath _). Defined.

Definition sectohfiber { X : UU } (P:X -> UU): (forall x:X, P x) -> (hfiber (fun f:_ => fun x:_ => pr1  (f x)) (fun x:X => x)) := (fun a : forall x:X, P x => tpair _ (fun x:_ => tpair _ x (a x)) (idpath (fun x:X => x))).

Definition hfibertosec { X : UU } (P:X -> UU):
  (hfiber (fun f x => pr1 (f x)) (fun x:X => x)) -> (forall x:X, P x)
  := fun se:_  => fun x:X => match se as se' return P x with tpair _ s e => (transportf P (toforallpaths _ (fun x:X => pr1 (s x)) (fun x:X => x) e x) (pr2  (s x))) end.

Definition sectohfibertosec { X : UU } (P:X -> UU): forall a: forall x:X, P x, paths (hfibertosec _  (sectohfiber _ a)) a := fun a:_ => (pathsinv0 (etacorrection _ _ a)).

(** Axiom statements (propositions) *)

Definition univalenceStatement := forall X Y:UU, isweq (@eqweqmap X Y).

Definition funextemptyStatement := forall (X:UU) (f g : X->empty), f = g.

Definition funextsecweqStatement :=
  forall (T:UU) (P:T -> UU) (f g :forall t:T, P t), isweq (toforallpaths _ f g).

Definition propositionalUnivalenceStatement :=
  forall P Q, isaprop P -> isaprop Q -> (P -> Q) -> (Q -> P) -> P=Q.

(** Axiom consequence statements (not propositions) *)

Definition funextsecStatement :=
  forall (T:UU) (P:T -> UU) (f g :forall t:T, P t), f ~ g -> f = g.

Definition funextfunStatement :=
  forall (X Y:UU) (f g : X -> Y), f ~ g -> f = g.

Definition weqtopathsStatement := forall ( T1 T2 : UU ), T1 ≃ T2 -> T1 = T2.

Definition weqpathsweqStatement (weqtopaths:weqtopathsStatement) :=
  forall ( T1 T2 : UU ) ( w : T1 ≃ T2 ), eqweqmap (weqtopaths _ _ w) = w.

(** Implications between statements and consequences of them *)

Theorem funextsecImplication : funextsecweqStatement -> funextsecStatement.
Proof.
  intros fe ? ? ? ?. exact (invmap (weqpair _ (fe _ _ f g))).
Defined.

Theorem funextfunImplication : funextsecStatement -> funextfunStatement.
Proof.
  intros fe ? ?. apply fe.
Defined.

(** We show that [ univalenceAxiom ] is equivalent to the axioms [ weqtopathsStatement ] and [ weqpathsweqStatement ] stated below . *)

Theorem univfromtwoaxioms :
  (Σ weqtopaths: weqtopathsStatement, weqpathsweqStatement weqtopaths)
  <-> univalenceStatement.
Proof.
  split.
  { intros [weqtopaths weqpathsweq] T1 T2.
    set ( P1 := fun XY : UU × UU => pr1 XY = pr2 XY ) .
    set ( P2 := fun XY :  UU × UU => weq (pr1 XY)  (pr2 XY) ) .
    set ( Z1 := total2 P1 ). set ( Z2 := total2 P2 ).
    set ( f := totalfun _ _ ( fun XY : UU × UU =>  @eqweqmap (pr1 XY) (pr2 XY)) : Z1 -> Z2 ) .
    set ( g := totalfun _ _ ( fun XY : UU × UU =>  weqtopaths (pr1 XY) (pr2 XY) ) : Z2 -> Z1 ) .
    assert (efg : funcomp g f ~ idfun _) .
    - intro z2 . induction z2 as [ XY e ] .
      unfold funcomp . unfold idfun . unfold g . unfold f . unfold totalfun . simpl .
      apply ( maponpaths ( fun w : weq ( pr1 XY) (pr2 XY) =>  tpair P2 XY w )
                       ( weqpathsweq ( pr1 XY ) ( pr2 XY ) e )) .
    - set ( h := fun a1 : Z1 =>  pr1 ( pr1 a1 ) ) .
      assert ( egf0 : forall a1 : Z1 ,  pr1 ( g ( f a1 ) ) = pr1 a1 ).
      + intro. apply idpath.
      + assert ( egf1 : forall a1 a1' : Z1 ,  paths ( pr1 a1' ) (  pr1 a1 ) ->  paths a1' a1 ).
        * intros.
          set ( X' :=  maponpaths pr1 X ).
          assert ( is : isweq h ).
          { simpl in h .  apply isweqpr1pr1 . }
          apply ( invmaponpathsweq ( weqpair h is ) _ _ X' ).
        * set ( egf := fun a1  => egf1 _ _ ( egf0 a1 ) ).
          set ( is2 := gradth _ _ egf efg ).
          apply ( isweqtotaltofib _ _ ( fun _ => eqweqmap) is2 ( dirprodpair T1 T2 ) ).
          }
  { intros ua.
    simple refine (_,,_).
    - intros ? ?. exact (invmap (weqpair _ (ua _ _))).
    - intros ? ?. exact (homotweqinvweq (weqpair _ (ua _ _))). }
Defined.

(** Conjecture :  the pair [weqtopaths] and [weqtopathsweq] in the proof above is well defined up to a canonical equality. **)

(** ** Transport theorem.

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceAxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)

Lemma isweqtransportf10 { X : UU } ( P : X -> UU ) { x x' : X } ( e :  paths x x' ) : isweq ( transportf P e ).
Proof. intros. destruct e.  apply idisweq. Defined.

Lemma isweqtransportb10 { X : UU } ( P : X -> UU ) { x x' : X } ( e :  paths x x' ) : isweq ( transportb P e ).
Proof. intros. apply ( isweqtransportf10 _ ( pathsinv0 e ) ). Defined.


Lemma l1  { X0 X0' : UU } ( ee : paths X0 X0' ) ( P : UU -> UU ) ( pp' : P X0' ) ( R : forall X X' : UU , forall w : weq X X' , P X' -> P X ) ( r : forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) : paths ( R X0 X0' ( eqweqmap ee ) pp' ) (  transportb P ee pp' ).
Proof. destruct ee. simpl. apply r. Defined.

(** the axioms themselves *)

Axiom univalenceAxiom : univalenceStatement.
Axiom funextemptyAxiom : funextemptyStatement.
Axiom funextAxiom : funextsecweqStatement.

(** provide some theorems based on the axioms  *)

Theorem univalence (X Y:UU) : (X=Y) ≃ (X≃Y).
Proof. exact (weqpair _ (univalenceAxiom X Y)). Defined.

Definition weqtopaths : weqtopathsStatement.
Proof.
  intros ? ?. exact (invmap (univalence _ _)).
Defined.
Arguments weqtopaths {_ _} _.

Definition weqpathsweq : weqpathsweqStatement (@weqtopaths).
Proof.
  intros ? ? w. exact (homotweqinvweq (univalence T1 T2) w).
Defined.
Arguments weqpathsweq {_ _} _.

(** ** Proof of the functional extensionality for functions from univalence *)

Theorem weqtransportb ( P : UU -> UU ) ( R : forall ( X X' : UU ) ( w :  weq X X' ) , P X' -> P X ) ( r : forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) :  forall ( X X' : UU ) ( w :  weq X X' ) ( p' : P X' ) , paths ( R X X' w p' ) (  transportb P ( weqtopaths w ) p' ).
Proof.
  intros. set ( uv := weqtopaths w ).   set ( v := eqweqmap uv ).
  assert ( e : paths v w ) . unfold weqtopaths in uv.
  apply ( homotweqinvweq ( weqpair _ ( univalenceAxiom X X' ) ) w ).
  assert ( ee : paths ( R X X' v p' ) ( R X X' w p' ) ) . set ( R' := fun vis : weq X X' => R X X' vis p' ). assert ( ee' : paths ( R' v ) ( R' w ) ). apply (  maponpaths R' e ). assumption.
  destruct ee. apply l1. assumption. Defined.

Corollary isweqweqtransportb ( P : UU -> UU ) ( R :  forall ( X X' : UU ) ( w :  weq X X' ) , P X' -> P X ) ( r :  forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) :  forall ( X X' : UU ) ( w :  weq X X' ) , isweq ( fun p' :  P X' => R X X' w p' ).
Proof.
  intros.
  assert ( e : forall p' : P X' , paths ( R X X' w p' ) (  transportb P ( weqtopaths w ) p' ) ).
  - apply weqtransportb. assumption.
  - assert ( ee : forall p' : P X' , paths  ( transportb P ( weqtopaths w ) p' ) ( R X X' w p' ) ).
    + intro. apply ( pathsinv0 ( e p' ) ).
    + clear e.
      assert ( is1 : isweq ( transportb P ( weqtopaths w ) ) ).
      apply isweqtransportb10.
      apply ( isweqhomot ( transportb P ( weqtopaths w ) ) ( fun p'  :  P X' => R X X' w p' ) ee is1 ).
Defined.

(** Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)

Theorem isweqcompwithweq { X X' : UU } ( w : weq X X' ) ( Y : UU ) :  isweq ( fun f : X' -> Y => ( fun x : X => f ( w x ) ) ).
Proof.
  set ( P := fun X0 : UU => ( X0 -> Y ) ).
  set ( R := fun X0 : UU => ( fun X0' : UU => ( fun w1 : X0 -> X0' =>  ( fun  f : P X0'  => ( fun x : X0 => f ( w1 x ) ) ) ) ) ).
  apply ( isweqweqtransportb P R (fun X0 f => idpath _) X X' w ).
Defined.

Lemma eqcor0 { X X' : UU } ( w :  weq X X' ) ( Y : UU ) ( f1 f2 : X' -> Y ) : paths ( fun x : X => f1 ( w x ) )  ( fun x : X => f2 ( w x ) ) -> paths f1 f2.
Proof. apply ( invmaponpathsweq ( weqpair _ ( isweqcompwithweq w Y ) ) f1 f2 ). Defined.

Lemma apathpr1topr ( T : UU ) : paths ( fun z :  pathsspace T => pr1 z ) ( fun z : pathsspace T => pr1 ( pr2 z ) ).
Proof. apply ( eqcor0 ( weqpair _ ( isweqdeltap T ) ) _ ( fun z :  pathsspace T => pr1 z ) ( fun z :  pathsspace T => pr1 ( pr2 z ) ) ( idpath ( idfun T ) ) ) . Defined.

Theorem funextfunPreliminary : funextfunStatement.
Proof.
  intros ? ? f1 f2 e.
  set ( f := fun x : X => pathsspacetriple Y ( e x ) ).
  set ( g1 := fun z : pathsspace Y => pr1 z ).
  set ( g2 := fun z : pathsspace Y => pr1 ( pr2 z ) ).
  change ( (funcomp f g1) = (funcomp f g2) ).
  apply maponpaths.
  apply apathpr1topr.
Defined.

Arguments funextfunPreliminary {_ _} _ _ _.

(** *** Deduction of functional extensionality for dependent functions (sections) from functional extensionality of usual functions *)

Lemma isweqlcompwithweq {X X' : UU} (w: weq X X') (Y:UU) : isweq (fun (a:X'->Y) x => a (w x)).
Proof.
  simple refine (gradth _ _ _ _).
  exact (fun b x' => b (invweq w x')).
  exact (fun a => funextfunPreliminary _ a (fun x' => maponpaths a (homotweqinvweq w x'))).
  exact (fun a => funextfunPreliminary _ a (fun x  => maponpaths a (homotinvweqweq w x ))).
Defined.

Lemma isweqrcompwithweq { Y Y':UU } (w: weq Y Y')(X:UU): isweq (fun a:X->Y => (fun x:X => w (a x))).
Proof. intros. set (f:= (fun a:X->Y => (fun x:X => w (a x)))). set (g := fun a':X-> Y' => fun x:X => (invweq  w (a' x))).
set (egf:= (fun a:X->Y => funextfunPreliminary (fun x:X => (g (f a)) x) a (fun x: X => (homotinvweqweq w (a x))))).
set (efg:= (fun a':X->Y' => funextfunPreliminary (fun x:X => (f (g a')) x) a' (fun x: X =>  (homotweqinvweq w (a' x))))).
apply (gradth  f g egf efg). Defined.

Theorem funcontr { X : UU } (P:X -> UU) : (forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x).
Proof. intros X0 . set (T1 := forall x:X, P x). set (T2 := (hfiber (fun f: (X -> total2 P)  => fun x: X => pr1  (f x)) (fun x:X => x))). assert (is1:isweq (@pr1 X P)). apply isweqpr1. assumption.  set (w1:= weqpair  (@pr1 X P) is1).
assert (X1:iscontr T2).  apply (isweqrcompwithweq  w1 X (fun x:X => x)).
apply ( iscontrretract  _ _  (sectohfibertosec P ) X1). Defined.

Corollary funcontrtwice { X : UU } (P: X-> X -> UU)(is: forall (x x':X), iscontr (P x x')): iscontr (forall (x x':X), P x x').
Proof. intros.
assert (is1: forall x:X, iscontr (forall x':X, P x x')). intro. apply (funcontr _ (is x)). apply (funcontr _ is1). Defined.


(** Proof of the fact that the [ toforallpaths ] from [paths s1 s2] to [forall t:T, paths (s1 t) (s2 t)] is a weak equivalence - a strong form
of functional extensionality for sections of general families. The proof uses only [funcontr] which is an axiom i.e. its type satisfies [ isaprop ].  *)

Lemma funextweql1 { T : UU } (P:T -> UU) (g: ∀ t, P t) : ∃! (f:∀ t, P t), ∀ t:T, f t = g t.
Proof.
  intros. unshelve refine (iscontrretract (X := ∀ t, Σ p, p = g t) _ _ _ _).
  - intros x. unshelve refine (_,,_).
    + intro t. exact (pr1 (x t)).
    + intro t; simpl. exact (pr2 (x t)).
  - intros y t. exists (pr1 y t). exact (pr2 y t).
  - intros u. induction u as [t x]. reflexivity.
  - apply funcontr. intro t. apply iscontrcoconustot.
Defined.

Theorem isweqtoforallpaths { T : UU } (P:T -> UU) (f g: ∀ t:T, P t) :
  isweq (toforallpaths _ f g).
Proof.
  intros.
  refine (isweqtotaltofib _ _ (λ (h:∀ t, P t), toforallpaths _ h g) _ f).
  refine (isweqcontrcontr (X := Σ (h: ∀ t, P t), h = g)
            (λ ff, tpair _ (pr1 ff) (toforallpaths P (pr1 ff) g (pr2 ff))) _ _).
  { exact (iscontrcoconustot _ g). }
  { apply funextweql1. }
Qed.

Theorem weqtoforallpaths { T : UU } (P:T -> UU)(f g : forall t:T, P t) :
  (f = g) ≃ (∀ t:T, f t = g t).
Proof. intros. exists (toforallpaths P f g). apply isweqtoforallpaths. Defined.

Definition funextsec : funextsecStatement.
Proof.
  intros ? ? f g.
  exact (invmap (weqtoforallpaths _ f g)).
Defined.
Arguments funextsec {_} _ _ _ _.

Theorem funextfun : funextfunStatement.
Proof.
  exact (funextfunImplication (@funextsec)).
Defined.

Arguments funextfun {_ _} _ _ _.

Theorem isweqfunextsec { T : UU } (P:T -> UU) (f g : forall t:T, P t) :
  isweq (funextsec P f g).
Proof. intros. apply (isweqinvmap (weqtoforallpaths _ f g)). Defined.

Definition weqfunextsec { T : UU } (P:T -> UU)(f g : forall t:T, P t) :
  weq  (forall t:T, paths (f t) (g t)) (paths f g)
  := weqpair _ ( isweqfunextsec P f g ) .
