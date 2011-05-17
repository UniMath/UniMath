(** * Introduction 

This file contains the (current state of) the mathematical library for the proof assistant Coq based on the Univalent Foundations.  
Univalent Foundations are inspired by the univalent model of type theory which interprets types as homotopy types, Martin-Lof equality as paths spaces and universes as bases of universal ("univalent") fibrations. For a detailed overview of the content see the table of content in univ_toc.html . 

I tried to keep the notations such that the names of types which are (expected to be) a property in the sense of being of h-level 1 start with "is"but I have not been very consistent about it.

There is an increasing number of theorems which have very short proofs based on the univalence axiom (see u01.v) which are given much longer proofs here. One hopes that eventually a mechnaical procedure for the replacement of proofs using the univalence axiom by proofs which only use it in some computationally uninformative ways will be found but until then I am not using the univalence axiom in any of the constructions. 


IMPORTANT: for those who may want to add to these files. There are some rules which have to be followed in creating new definitions and theorems which at the moment are not tracked by the proof checker.

1. The current system of Coq is not completely compatible with the univalent semantics. The problem (the only one as far as I know) lies in the way the universe levels (u-levels) are assigned to the objects defined by the inductive definitions of the form

Inductive Ind (...)...(...): A -> Type := ...


The current u-level assignemet takes into account the u-levels of the constructors but not the u-level of A. To ensure compatibility with the univalent model the u-level of Ind should be no less than the u-level of A. The u-levels of the parameters (the types appearing in (...)...(...) ) do not matter. 

A particular case of this problem is the "singleton elimination" rule which provides a good example of this incompatibility. The inductive definition of the identity types which uses one of the points as a parametr has A=:T (the underlying type) but since no mention of T appears in the constructor the system considers that there are no u-level restrictions on the resulting object and in particular that it can be placed in Prop while still having the full Ind_rect elimninator (see elimination, singleton elimination in the Index to the Refernce Manual). 

Since in the present approach the universe management is made explicit one has:

RULE 1 Do not use inductive definitions of the form 

Inductive Ind (...)...(...): A -> UU := ...

unless all the "arguments" of A can be typed to UU. 


2. While it does not lead directly to any contradictions the shape of the foundations suggests very strongly that at the moment it is best to completely avoid the use of the universes Prop and Set. Instead we should use the the conditions isaprop and isaset which are applicable to the types of any of the type universes.  

*)









(** * Preambule. *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Definition UU:=Type. (* This fixes a type universe which we will be working with. *)


(* We are using the standard library definitions for unit (one point set), Empty_set and nat (the set of natural numbers). *)

Definition empty:=Empty_set.

Definition initmap (X:UU) : empty -> X.
Proof. intros.  destruct H. Defined. 



(** * Some standard constructions not using equality. *)

(**  ** Dependent sums (fibrations) *)


Inductive total2 (T:UU) (P:T -> UU) : UU := tpair: forall t:T, forall x: P t, total2 T P.


Definition pr21 (T:UU) (P:T -> UU) (z: total2 T P) : T := 
match z with 
tpair t x => t
end.  


Definition pr22 (T:UU) (P:T -> UU) (z: total2 T P) : P (pr21 _ _ z):=
match z with
tpair t x => x
end. 



(** ** Pairwise direct products. *)




Definition dirprod (X:UU)(Y:UU):= total2 X (fun x:X => Y).
Definition dirprodpair (X:UU)(Y:UU):= tpair X (fun x:X => Y).

Definition dirprodadj (X Y Z:UU): ((dirprod X Y) -> Z) -> (X -> Y -> Z) := fun f:_ => fun x:X => fun y:Y => f (dirprodpair _ _ x y).


Definition dirprodf (X Y X' Y':UU)(f:X-> Y)(f':X' -> Y'): dirprod X X' -> dirprod Y Y':= fun xx':_ => match xx' with tpair x x' => dirprodpair _ _ (f x) (f' x') end. 


Definition ddualand (X Y P:UU)(xp: (X -> P) -> P)(yp: (Y -> P) -> P): ((dirprod X Y) -> P) -> P.
Proof. intros. set (int1 := fun ypp:((Y->P)->P) => fun x:X => yp (fun y:Y => X0 (dirprodpair _ _ x y))).   apply (xp (int1 yp)). Defined. 


(** ** Basic results on negation and double negation. *)


(**  Basic constructions related to the adjoint evaluation function [X -> ((X -> Y) -> Y)]. *)


Definition adjev (X Y:UU): X -> ((X -> Y)->Y) := fun x:X => fun f:_ => f x.

Definition adjev2 (X Y:UU): (((X -> Y) -> Y) ->Y) -> (X -> Y)  := fun phi:_ => (fun x:X => phi (fun f:X -> Y => f x)).



(** Negation and double negation. *)


Definition neg (X:UU):= X -> empty.

Definition negf (X:UU)(Y:UU)(f:X -> Y): (neg Y) -> (neg X):= fun phi:Y -> empty => fun x:X => phi (f x).

Definition dneg (X:UU):= (X-> empty)->empty.

Definition dnegf (X:UU)(Y:UU)(f:X->Y): (dneg X) -> (dneg Y):= negf _ _ (negf _ _ f).

Definition todneg (X:UU): X -> (dneg X):= adjev X empty. 

Definition dnegnegtoneg (X:UU): dneg (neg X) -> neg X := negf _ _  (todneg X).

Lemma dneganddnegl1 (X:UU)(Y:UU): dneg X -> dneg Y -> (X -> neg Y) -> empty.
Proof. intros. assert (dneg X -> neg Y). apply (fun xx: dneg X => dnegnegtoneg _ (dnegf _ _ X2 xx)).  apply (X1 (X3 X0)). Defined.

Definition dneganddnegimpldneg (X:UU)(Y:UU)(dx: dneg X)(dy:dneg Y): dneg (dirprod X Y):= ddualand X Y empty dx dy. 













(** * Paths (equalities) and operations on paths *)




Inductive paths (T:UU)(t:T): T -> UU := idpath: paths T t t.


Definition pathscomp0 (T:UU) (a:T)(b:T) (c:T)(e1: paths _ a b)(e2:paths _ b c): paths _ a c.
Proof. intros. induction e1.  assumption. Defined.

Definition pathscomp0rid  (T:UU) (a:T)(b:T)(e1: paths _ a b): paths _ (pathscomp0 _ _ b b e1 (idpath _ b)) e1. 
Proof. intros.  induction e1. simpl. apply idpath.  Defined. 

Definition pathsinv0 (T:UU) (a:T) (b:T)(e: paths _ a b): paths _ b a.
Proof. intros. induction e.  apply idpath. Defined. 

Definition pathsinv0l1 (X:UU)(a:X)(b:X)(e: paths _ a b): paths _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ e) e) (idpath _ _).
Proof. intros. induction e. simpl. apply idpath. Defined. 

Definition pathsinv0inv0 (X:UU)(x x':X)(e: paths _ x x'): paths _ (pathsinv0 _ _ _ (pathsinv0 _ _ _ e)) e.
Proof. intros. destruct e. simpl. apply idpath. Defined.  

Definition pathsinv0r1 (X:UU)(a:X)(b:X)(e: paths _ a b): paths _ (pathscomp0 _ _ _ _ e (pathsinv0 _ _ _ e)) (idpath _ _).
Proof. intros. induction e. simpl.  apply idpath. Defined. 

Definition pathsinv1r (T:UU)(a:T)(b:T)(c:T)(e1:paths _ a b)(e2: paths _ b c): paths _ (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e1 e2) (pathsinv0 _ _ _  e2)) e1.
Proof. intros. induction e1. simpl. induction e2. simpl. apply idpath.  Defined. 

Definition pathsinv1l (T:UU)(a:T)(b:T)(c:T)(e1:paths _ a b)(e2: paths _ b c): paths _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _  e1) (pathscomp0 _ _ _ _ e1 e2))  e2.
Proof. intros.  induction e2. simpl.  induction e1. simpl.  apply idpath. Defined. 


Definition pathscomp021  (T:UU) (a:T)(b:T) (c:T)(e11: paths _ a b)(e12: paths _ a b)(ee1: paths _ e11 e12)(e2:paths _ b c): paths _ (pathscomp0 _ _ _ _ e11 e2) (pathscomp0 _ _ _ _ e12 e2).
Proof. intros. induction ee1.  apply idpath. Defined. 


Definition maponpaths: forall T1:UU, forall T2:UU, forall f:T1 -> T2, forall t11:T1, forall t12:T1, (paths T1 t11 t12) -> (paths T2 (f t11) (f t12)).
Proof. intros.  induction X. apply idpath. Defined. 

Lemma idtoid1: forall T1:UU, forall T2:UU, forall f:T1 -> T2, forall t1:T1, paths (paths T2 (f t1) (f t1)) (maponpaths _ _ f t1 t1 (idpath T1 t1)) (idpath T2 (f t1)).
Proof. intros. unfold maponpaths. simpl. apply idpath. Defined. 


Definition maponpathscomp0 (X:UU)(Y:UU)(f:X -> Y)(x1:X)(x2:X)(x3:X)(e1: paths _ x1 x2)(e2: paths _ x2 x3): paths _ (maponpaths _ _ f _ _ (pathscomp0 _ _ _ _ e1 e2)) (pathscomp0  _ _ _ _ (maponpaths _ _ f _ _ e1) (maponpaths _ _ f _ _ e2)).
Proof. intros.  induction e1. induction e2.  simpl. apply idpath. Defined. 

Definition maponpaths2a (X:UU)(Y:UU)(Z:UU)(f1:X-> Y)(f2:X->Y)(g:Y -> Z): paths _ f1 f2 -> paths _ (fun x:X => (g (f1 x))) (fun x:X => (g (f2 x))).
Proof. intros. set (int1:= (fun f: X-> Y => (fun x:X => (g (f x))))).  apply (maponpaths _ _ int1 _ _ X0). Defined.

Definition maponpaths2b (X:UU)(Y:UU)(Z:UU)(f:X-> Y)(g1:Y->Z)(g2:Y -> Z): paths _ g1 g2 -> paths _ (fun x:X => (g1 (f x))) (fun x:X => (g2 (f x))).
Proof. intros. set (int1:= (fun g: Y-> Z => (fun x:X => (g (f x))))).  apply (maponpaths _ _ int1 _ _ X0). Defined. 


Lemma maponpathsidfun (X:UU)(x:X)(x':X)(e:paths _ x x'): paths _ (maponpaths _ _ (fun x:X => x) _ _ e) e. 
Proof. intros. simpl. induction e. apply (idtoid1 _ _ (fun x:X => x) x). Defined. 

Lemma maponpathsfuncomp (X:UU)(Y:UU)(Z:UU)(f:X-> Y)(g:Y->Z)(x:X)(x':X)(e: paths _ x x'): paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ e)) (maponpaths _ _ (fun x:X => (g (f x))) _ _ e).
Proof. intros. induction e. unfold maponpaths.  simpl. apply idpath. Defined. 


(** The following four statements show that maponpaths defined by a function f which is homotopic to the identity is "surjective". It is later used to show that the maponpaths defined by a function which is a weak equivalence is itself a weak equivalence. *) 


Definition maponpathshomidinv (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X): paths _ (f x) (f x') -> paths _ x x' := (fun e: paths _ (f x) (f x') => pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))).


Lemma maponpathshomid1 (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ x x'): paths _ (maponpaths _ _ f _ _ e) (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ e (pathsinv0 _ _ _ (h x')))).
Proof. intros. induction e. change (pathscomp0 X x x (f x) (idpath X x) (pathsinv0 X (f x) x (h x))) with (pathsinv0 X (f x) x (h x)). assert (ee: paths _  (maponpaths X X f x x (idpath X x)) (idpath _ (f x))). apply idtoid1. 
assert (eee: paths _ (idpath _ (f x)) (pathscomp0 X (f x) x (f x) (h x)  (pathsinv0 X (f x) x (h x)))). apply (pathsinv0 _ _ _ (pathsinv0r1 _ _ _ (h x))). apply (pathscomp0 _ _ _ _ ee eee). Defined. 


Lemma maponpathshomid12 (X:UU)(x:X)(x':X)(fx:X)(fx':X)(e:paths _ fx fx')(hx:paths _ fx x)(hx':paths _ fx' x'): paths _   (pathscomp0 _ _ _ _ (hx) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (hx)) (pathscomp0 _ _ _ _ e (hx'))) (pathsinv0 _ _ _ (hx')))) e.
Proof. intros. induction hx. induction hx'. induction e.  simpl. apply idpath. Defined. 


Lemma maponpathshomid2 (X:UU)(f:X->X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ (f x) (f x')): paths _ (maponpaths _ _ f _ _ (maponpathshomidinv _ f h _ _ e)) e.
Proof.  intros. assert (ee: paths _ (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))) (pathsinv0 _ _ _ (h x')))) e). apply (maponpathshomid12 _ _ _ (f x) (f x') e (h x) (h x')). assert (eee: paths _ (maponpaths _ _ f _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x')))) (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))) (pathsinv0 _ _ _ (h x'))))). apply maponpathshomid1. apply (pathscomp0 _ _ _ _ eee ee). Defined. 


(** Here we consider the behavior of maponpaths in the case of a projection p with a section s. *)


Definition pathssec1 (X: UU)(Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _  (p (s x)) x): forall x:X, forall y:Y, paths _ (s x) y -> paths _ x (p y).
Proof. intros. set (e:= maponpaths _ _ p _ _ X0). apply (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (eps x)) e). Defined.


Definition pathssec2 (X: UU)(Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x): forall x:X, forall x':X, paths _ (s x) (s x') -> paths _ x x'.
Proof. intros. set (e:= pathssec1 _ _ s p eps _ _ X0).  apply (pathscomp0 _ _ _ _ e (eps x')). Defined.

Definition pathssec2id (X: UU)(Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x): forall x:X, paths _ (pathssec2 _ _ s p eps _ _ (idpath _ (s x))) (idpath _ x).
Proof. intros. unfold pathssec2. unfold pathssec1. simpl. assert (e: paths _ (pathscomp0 X x (p (s x)) (p (s x)) (pathsinv0 X (p (s x)) x (eps x)) (idpath X (p (s x)))) (pathsinv0 X (p (s x)) x (eps x))). apply pathscomp0rid. assert (ee: paths _ 
(pathscomp0 X x (p (s x)) x (pathscomp0 X x (p (s x)) (p (s x)) (pathsinv0 X (p (s x)) x (eps x)) (idpath X (p (s x)))) (eps x)) 
(pathscomp0 X x (p (s x)) x (pathsinv0 X (p (s x)) x (eps x)) (eps x))). 
apply (maponpaths _ _ (fun e0: _ => pathscomp0 X x (p (s x)) x e0  (eps x)) _ _ e). assert (eee: paths _ (pathscomp0 _ _ _ _ (pathsinv0 X (p (s x)) x (eps x)) (eps x)) (idpath _ x)).  apply (pathsinv0l1 _ _ _ (eps x)). apply (pathscomp0 _ _ _ _ ee eee). Defined. 


Definition pathssec3 (X: UU)(Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x): forall x:X, forall x':X, forall e: paths _ x x', paths _  (pathssec2 _ _ s p eps _ _ (maponpaths _ _ s _ _ e)) e.
Proof. intros. induction e.  simpl. unfold pathssec2. unfold pathssec1.  simpl. apply pathssec2id.  Defined. 












(** * Fibrations and paths. *)


Definition tppr (T:UU)(P:T -> UU)(x: total2 T P): paths _ x (tpair _ _ (pr21 _ _ x) (pr22 _ _ x)).
Proof. intros. induction x. apply idpath. Defined. 


Definition constr1 (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): total2 (P x -> P x') (fun f: P x -> P x' => (total2 (forall p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p))) (fun ee: forall p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p)) => forall pp: P x, paths _ (maponpaths _ _ (pr21 X P) _ _ (ee pp)) e))). 
Proof. intros. induction e. split with (fun p: P x => p). simpl. split with (fun p: P x => idpath _ _). unfold maponpaths. simpl. apply (fun pp: P x => idpath _ _ ). Defined. 


Definition transportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x -> P x' := pr21 _ _ (constr1 X P x x' e).

Lemma  transportfid (X:UU)(P:X -> UU)(x:X)(p: P x): paths _ (transportf _ P _ _ (idpath _ x) p) p.
Proof. intros. unfold transportf. unfold constr1.  simpl. apply idpath. Defined. 


Definition transportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x' -> P x := transportf _ P x' x (pathsinv0 _ _ _ e).


Lemma functtransportf (X:UU)(Y:UU)(f:X->Y)(P:Y->UU)(x:X)(x':X)(e: paths _ x x')(p: P (f x)): paths _ (transportf _ (fun x:X => P (f x)) x x' e p) (transportf _ P (f x) (f x') (maponpaths _ _ f _ _ e) p).
Proof.  intros.  induction e. apply idpath. Defined.   



(** * First homotopy notions *)


(** ** Contractibility, homotopy fibers etc. *)



Definition iscontr (T:UU) : UU := total2 T (fun cntr:T => forall t:T, paths T t cntr).

Definition iscontrpair (T:UU) (cntr: T) (e: forall t:T, paths T t cntr) : iscontr T := tpair T  (fun cntr:T => forall t:T, paths T t cntr) cntr e. 



Lemma contrl1 (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y y (f(g y))): iscontr X -> iscontr Y.
Proof. intros.  destruct X0.  set (y:= f t).  split with y.  intros.  
assert (e1: paths _ (f (g t0)) y). apply (maponpaths _ _ f _ _ (x (g t0))).
assert (e2: paths _ t0 (f (g t0))). apply (efg t0).
induction e2.  assumption.  Defined. 


Lemma contrl1' (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y): iscontr X -> iscontr Y.
Proof. intros. set (efg' := fun y:Y => pathsinv0 _ _ _ (efg y)).  apply contrl1 with X f g. assumption. assumption. Defined.

Lemma contrl2 (X:UU)(is: iscontr X)(x:X)(x':X): paths _ x x'.
Proof. intros. unfold iscontr in is.  induction is. set (e:= x0 x). set (e':= pathsinv0 _ _ _ (x0 x')). apply (pathscomp0 _ _ _ _ e e'). Defined. 


Definition coconustot (T:UU) (t:T) := total2 T (fun t':T => paths T t' t).
Definition coconustotpair (T:UU) (t:T) (t':T) (e: paths T t' t):coconustot T t := tpair T (fun t':T => paths T t' t) t' e.

Lemma connectedcoconustot: forall T:Type, forall t:T, forall e1: coconustot T t, forall e2:coconustot T t, paths (coconustot T t) e1 e2.
Proof. intros. destruct e1. destruct x. destruct e2. destruct x. apply idpath. Defined. 

Lemma iscontrcoconustot (T:UU) (t:T) : iscontr (coconustot T t).
Proof. intros. unfold iscontr.  set (t0:= tpair _ (fun t':T => paths T t' t) t (idpath T t)).  split with t0. intros. apply  connectedcoconustot. Defined.



Definition coconusfromt (T:UU)(t:T) :=  total2 T (fun t':T => paths T t t').
Definition coconusfromtpair (T:UU) (t:T) (t':T) (e: paths T t t'):coconusfromt T t := tpair T (fun t':T => paths T t t') t' e.

Lemma connectedcoconusfromt: forall T:UU, forall t:T, forall e1: coconusfromt T t, forall e2:coconusfromt T t, paths (coconusfromt T t) e1 e2.
Proof. intros. destruct e1. destruct x. destruct e2. destruct x. apply idpath. Defined.

Lemma iscontrcoconusfromt (T:Type) (t:T) : iscontr (coconusfromt T t).
Proof. intros. unfold iscontr.  set (t0:= tpair _ (fun t':T => paths T t t') t (idpath T t)).  split with t0. intros. apply  connectedcoconusfromt. Defined.



Definition pathsspace (T:UU) := total2 T (fun t:T => coconusfromt _ t).
Definition pathsspacetriple (T:UU) (t1:T)(t2:T)(e: paths _ t1 t2): pathsspace T := tpair _ _  t1 (coconusfromtpair _ _ t2 e). 

Definition deltap (T:UU) : T -> pathsspace T := (fun t:T => pathsspacetriple _ t t (idpath _ t)). 

Definition pathsspace' (T:UU) := total2 (dirprod T T) (fun xy:_ => (match xy with tpair x y => paths _ x y end)).


Definition hfiber (X:UU)(Y:UU)(f:X -> Y)(y:Y) : UU := total2 X (fun pointover:X => paths Y (f pointover) y). 
Definition hfiberpair  (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e: paths Y (f x) y): hfiber _ _ f y := tpair X  (fun pointover:X => paths Y (f pointover) y) x e.


Lemma hfibertriangle1 (X Y:UU)(f:X -> Y)(y:Y)(xe1 xe2: hfiber _ _ f y)(e: paths _ xe1 xe2): paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (maponpaths (hfiber _ _ f y) X  (pr21 _ _ ) _ _ e)) (pr22 _ _ xe2)).
Proof. intros. destruct e.  simpl. apply idpath. Defined. 


Lemma hfibertriangle2 (X Y:UU)(f:X -> Y)(y:Y)(xe1 xe2: hfiber _ _ f y)(ee: paths _ (pr21 _ _ xe1) (pr21 _ _ xe2))(eee: paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ ee) (pr22 _ _ xe2))): paths _ xe1 xe2.
Proof. intros. destruct xe1. destruct xe2.   simpl in eee. simpl in ee. destruct ee. simpl in eee. apply (maponpaths _ _ (fun e: paths _ (f t) y => hfiberpair _ _ f y t e) _ _ eee). Defined. 


Definition constr3 (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e1: paths _ (f x) y)(e2: paths _ (f x) y) (ee: paths _  e1 e2): paths _ (hfiberpair _ _ _ _ x e1) (hfiberpair _ _ _ _ x e2).
Proof. intros. destruct ee. apply idpath.  Defined.


Definition coconusf (X Y:UU) (f: X -> Y):= total2 Y (fun y:_ => hfiber _ _ f y).


Definition fromcoconusf (X Y:UU)(f: X -> Y) : coconusf _ _ f -> X := fun yxe:_ => pr21 _ _ (pr22 _ _ yxe).

Definition tococonusf (X Y:UU)(f: X -> Y) : X -> coconusf _ _ f := fun x:_ => tpair _ _ (f x) (hfiberpair _ _ _ _ x (idpath _ _)).   


(** ** Weak equivalences *)

(** *** Basics. *)


Definition isweq (X:UU)(Y:UU)(F:X -> Y) : UU := forall y:Y, iscontr (hfiber X Y F y) .

Definition invmap (X:UU) (Y:UU) (f:X-> Y) (isw: isweq X Y f): Y->X.
Proof. intros. unfold isweq in isw. apply (pr21 _ _ (pr21 _ _ (isw X0))). Defined.

Lemma idisweq (T:UU) : isweq T T (fun t:T => t).
Proof. intros. 
unfold isweq.
intros.
assert (y0: hfiber T T (fun t : T => t) y). apply (tpair T (fun pointover:T => paths T ((fun t:T => t) pointover) y) y (idpath T y)). 
split with y0. intros.  
destruct y0.    destruct t.  induction x.  induction x0.  apply idpath. Defined. 

Definition weq (X:UU)(Y:UU) : UU := total2 (X -> Y) (fun f:X->Y => isweq X Y f) .
Definition weqpair (X:UU)(Y:UU)(f:X-> Y)(is: isweq X Y f) : weq X Y := tpair (X -> Y) (fun f:X->Y => isweq X Y f) f is. 
Definition idweq (X:UU) : weq X X :=  tpair (X-> X)  (fun f:X->X => isweq X X f) (fun x:X => x) ( idisweq X ) .


Definition isweqtoempty (X:UU)(f:X -> empty): isweq _ _ f.
Proof. intros. intro.  apply (initmap _ y). Defined. 


(** We now define different homotopies and maps between the paths spaces corresponding to a weak equivalence. What may look like unnecessary complexity in the  definition of weqgf is due to the fact that the "naive" definition, that of weqgf00, needs to be corrected in order for the lemma weqfgf to hold. *)



Definition weqfg (T1:UU) (T2:UU) (f:T1-> T2) (is1: isweq _ _ f): forall t2:T2, paths T2 (f ((invmap _ _ f is1) t2)) t2.
Proof. intros. unfold invmap. simpl. unfold isweq in  is1. apply (pr22 _ _  (pr21 _ _  (is1 t2))). Defined.


Definition weqgf0  (X Y:UU) (f:X -> Y) (is: isweq _ _ f)(x:X): paths _ x (invmap _ _ f is (f x)).
Proof. intros. unfold isweq in is.  set (isfx:= is (f x)). set (pr21fx:= pr21 X (fun x':X => paths _ (f x') (f x))).
set (xe1:= (hfiberpair _ _ f (f x) x (idpath _ (f x)))). apply  (maponpaths _ _ pr21fx _ _ (pr22 _ _ isfx xe1)). Defined.

Definition weqgf (X Y:UU) (f:X -> Y) (is: isweq _ _ f)(x:X): paths _ (invmap _ _ f is (f x)) x := pathsinv0 _ _ _ (weqgf0 _ _ f is x).

Lemma diaglemma2 (X Y:UU)(f:X -> Y)(x x':X)(e1: paths _ x x')(e2: paths _ (f x') (f x))(ee: paths _ (idpath _ (f x)) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ e1) e2)): paths _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ e1)) e2.
Proof. intros.  induction e1. simpl. simpl in ee. assumption. Defined. 

Definition weqfgf (X:UU) (Y:UU) (f:X-> Y) (is: isweq _ _ f): forall x:X, paths _  (maponpaths _ _ f _ _ (weqgf _ _ f is x)) (weqfg _ _ f is (f x)).
Proof. intros. set (isfx:= is (f x)). set (xe1:= hfiberpair _ _ f (f x) x (idpath _ (f x))).  set (xe2:= pr21 _ _ isfx). set (e:= pr22 _ _ isfx xe1). set (ee:=hfibertriangle1 _ _ f (f x) xe1 xe2 e). simpl in ee. change  
               (maponpaths (hfiber X Y f (f x)) X
                  (pr21 X (fun pointover : X => paths Y (f pointover) (f x)))
                  xe1 xe2 e) with (weqgf0 _ _ f is x) in ee. change  (pr22 X (fun pointover : X => paths Y (f pointover) (f x)) xe2) with  (weqfg X Y f is (f x)) in ee. 
apply (diaglemma2 _ _ f _ _  (weqgf0 X Y f is x) (weqfg X Y f is (f x)) ee). Defined.



Definition pathsweq2 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, forall x':X, paths _ (f x) (f x') -> paths _ x x':= pathssec2 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq2id (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, paths _ (pathsweq2 _ _ f is1 _ _ (idpath _ (f x))) (idpath _ x):= pathssec2id X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).


Definition pathsweq1 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, forall y:Y, paths _ (f x) y -> paths _ x (invmap _ _ f is1 y):= pathssec1 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq1' (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): forall x:X, forall y:Y, paths _ x (invmap _ _ f is1 y) -> paths _ (f x) y:=
fun x:X => fun y:Y => fun e:_ => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ e) (weqfg _ _ f is1 y).


Definition pathsweq3 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f):  forall x:X, forall x':X, forall e: paths _ x x', paths _  (pathsweq2 _ _ f is1 _ _ (maponpaths _ _ f _ _ e)) e:= pathssec3 X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq4  (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f):forall x:X, forall x':X, forall e: paths _ (f x) (f x'), paths _ (maponpaths _ _ f _ _ (pathsweq2 _ _ f is1 _ _ e)) e.  
Proof. intros. set (g:=invmap _ _ f is1). set (gf:= fun x:X => (g (f x))).  set (ee:= maponpaths _ _ g _ _ e). set (eee:= maponpathshomidinv _  gf (weqgf _ _ f is1) _ _ ee). assert (e1: paths _ (maponpaths _ _ f _ _ eee) e). assert (e2: paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ eee)) (maponpaths _ _ g _ _ e)). assert (e3: paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ eee)) (maponpaths _ _ gf _ _ eee)). apply maponpathsfuncomp. assert (e4: paths _ (maponpaths _ _ gf _ _ eee) ee). apply maponpathshomid2. apply (pathscomp0 _ _ _ _ e3 e4). 
set (s:= maponpaths _ _ g (f x) (f x')). set (p:= pathssec2 _ _ g f (weqfg _ _ f is1) (f x) (f x')). set (eps:= pathssec3 _ _ g f (weqfg _ _ f is1) (f x) (f x')).  apply (pathssec2 _ _ s p eps _ _ e2). assert (e4: paths _ (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' e)) (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee)))). apply (pathsinv0 _ _ _ (maponpaths _ _ (fun e0: paths _ (f x) (f x') => (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' e0))) _ _ e1)). assert (paths _  (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee)) eee). apply (pathsweq3 _ _ f is1). assert (e6: paths _ (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee))) (maponpaths _ _ f _ _ eee)). apply (maponpaths _ _ (fun eee0: paths _ x x' => maponpaths _ _ f _ _ eee0) _ _ X0). set (e7:= pathscomp0 _ _ _ _ e4 e6). set (pathscomp0 _ _ _ _ e7 e1). assumption. Defined. 










(** Weak equivalences between contractible types (other implications are proved below). *)



Lemma iscontrxifiscontry (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr Y -> iscontr X.
Proof. intros. apply (contrl1 _ _ (invmap _ _ f is1) f (weqgf0 _ _ f is1) X0).  Defined. 




(** Functions between fibers defined by a path on the base are weak equivalences. *)






Lemma isweqtransportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportf X P x x' e).
Proof. intros. induction e. apply idisweq. Defined. 


Lemma isweqtransportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportb X P x x' e).
Proof. intros. apply (isweqtransportf _ _ _ _ (pathsinv0 _ _ _ e)). Defined. 





(** A type T:UU is contractible if and only if T -> unit is a weak equivalence. *)



Lemma unitl0: paths unit tt tt -> coconustot unit tt.
Proof. intros. apply (coconustotpair unit tt tt X). Defined.

Lemma unitl1: coconustot unit tt -> paths unit tt tt.
Proof. intros. induction X. induction t. assumption.  Defined.

Lemma unitl2: forall e: paths unit tt tt, paths (paths unit tt tt) (unitl1 (unitl0 e)) e.
Proof. intros. unfold unitl0. simpl. eapply idpath.  Defined.

Lemma unitl3: forall e:paths unit tt tt, paths (paths unit tt tt) e (idpath unit tt).
Proof. intros.
assert (e0: paths (coconustot unit tt) (unitl0 (idpath unit tt)) (unitl0 e)). eapply connectedcoconustot.
assert (e1:paths (paths unit tt tt) (unitl1 (unitl0 (idpath unit tt)))
    (unitl1 (unitl0 e))).   apply (maponpaths (coconustot unit tt) (paths unit tt tt) unitl1 (unitl0 (idpath unit tt)) (unitl0 e)  e0).    
assert (e2:  paths (paths unit tt tt) (unitl1 (unitl0 e)) e). eapply unitl2.
assert (e3: paths (paths unit tt tt)  (unitl1 (unitl0 (idpath unit tt))) (idpath unit tt)). eapply unitl2.
 induction e1. clear e0. induction e2. assumption.  Defined. 


Theorem iscontrunit: iscontr (unit).
Proof. assert (pp:forall x:unit, paths unit x tt). intros. induction x. apply (idpath _ _).
apply (tpair unit (fun cntr:unit => forall t:unit, paths unit  t cntr) tt pp). Defined. 


Lemma ifcontrthenunitl0: forall e1: paths unit tt tt, forall e2: paths unit tt tt, paths (paths unit tt tt) e1 e2.
Proof. intros. assert (e3: paths (paths unit tt tt) e1 (idpath unit tt) ). apply unitl3.
assert (e4: paths (paths unit tt tt) e2 (idpath unit tt)). apply unitl3. induction e3.  induction e4. apply idpath. Defined. 

Lemma isweqcontrtounit: forall T:UU, (iscontr T) -> (isweq T unit (fun t:T => tt)).
Proof. intros. unfold isweq. intros. induction y.
assert (c: hfiber T unit (fun x:T => tt) tt). induction X. eapply (hfiberpair T unit _ tt t (idpath unit tt)).
assert (e: forall d: (hfiber T unit (fun x:T => tt) tt), paths _ d c). intros. induction c. induction d. 
assert (e': paths (paths unit tt tt) x x0). apply ifcontrthenunitl0.
assert (e'': paths T t t0). destruct X. 
assert (e''': paths T t t1). apply x1.
assert (e'''': paths T t0 t1). apply x1. 
induction e''''. assumption.
induction e''. induction e'. apply idpath. apply (iscontrpair _ c e). Defined. 


Theorem iscontrifweqtounit (X:UU): weq X unit -> iscontr X.
Proof. intros.  apply (iscontrxifiscontry X unit _ (pr22 _ _ X0)). apply iscontrunit. Defined. 




(** *** A homotopy equivalence is a weak equivalence *)


Definition hfibersgftog (X:UU) (Y:UU) (Z:UU) (f:X -> Y) (g: Y -> Z) (z:Z) : hfiber _ _ (fun x:X => g(f x)) z -> hfiber _ _ g z.
Proof. intros. destruct X0. apply (hfiberpair _ _ g z (f t) x).  Defined. 


Lemma constr2 (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y) (z: X): forall z0: (hfiber _ _ g z), total2 (hfiber _ _ (fun x:X => g(f x)) z) (fun z':_ => paths _ z0 (hfibersgftog _ _ _ f g z z')). 
Proof. intros.  destruct z0. rename x into e. rename t into y. 

assert (eint: paths Y y (f z)).  assert (e0: paths Y (f(g y)) y). apply efg. assert (e1: paths Y (f(g y)) (f z)). apply (maponpaths _ _  f _ _ e). induction e1.  apply pathsinv0. assumption. 

set (int1:=constr1 Y (fun y:Y => paths X (g y) z) y (f z) eint). destruct int1.
set (int2:=hfiberpair _ _ (fun x0 : X => g (f x0)) z z (t e)).   split with int2.  apply x.  Defined. 


Lemma isweql1  (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y) (z: X): iscontr (hfiber _ _ (fun x:X => g(f x)) z) ->iscontr (hfiber _ _ g z).
Proof. intros. set (X1:= hfiber _ _ (fun x:X => g(f x)) z). set (Y1:= hfiber _ _ g z). set (f1:= hfibersgftog _ _ _ f g z). set (g1:= fun z0:_ => pr21 _ _ (constr2 _ _ f g efg z z0)). 
set (efg1:= (fun y1:Y1 => pr22 _ _ (constr2 _ _ f g efg z y1))).  simpl in efg1. apply (contrl1 _ _ f1 g1 efg1). assumption.   Defined. 


Lemma isweql2 (X:UU)(Y:UU)(f1:X-> Y) (f2:X->Y) (h: forall x:X, paths _ (f2 x) (f1 x))(y:Y): iscontr (hfiber _ _ f2 y) -> iscontr (hfiber _ _ f1 y).
Proof. intros. 

set (f:= (fun z:(hfiber _ _ f1 y) =>
match z with 
(tpair x e) => hfiberpair _ _ f2 y x (pathscomp0 _ _ _ _ (h x) e)
end)). 

set (g:= (fun z:(hfiber _ _ f2 y) =>
match z with
(tpair x e) => hfiberpair _ _ f1 y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) e)
end)). 

assert (egf: forall z:(hfiber _ _ f1 y), paths _ (g (f z)) z). intros. destruct z.  rename x into e. rename t into x.

apply (constr3 _ _ f1 y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ (h x) e)) e (pathsinv1l _ (f2 x) (f1 x) y (h x) e)).

apply (contrl1' _ _ g f egf X0). Defined.

Corollary isweqhomot (X:UU)(Y:UU)(f1:X-> Y) (f2:X->Y) (h: forall x:X, paths _ (f1 x) (f2 x)): isweq _ _ f1 -> isweq _ _ f2.
Proof. intros. unfold isweq. intro. set (Y0:= X0 y).  apply (isweql2 _ _ f2 f1 h). assumption. Defined. 



Theorem gradth (X:UU)(Y:UU)(f:X->Y)(g:Y->X)(egf: forall x:X, paths _ (g (f x)) x)(efg: forall y:Y, paths _ (f (g y)) y ): isweq _ _ f.
Proof. intros.  unfold isweq.  intros. rename y into z. 
assert (iscontr (hfiber _ _ (fun y:Y => (f (g y))) z)). 
assert (efg': forall y:Y, paths _ y (f (g y))). intros. set (e1:= efg y). apply pathsinv0. assumption. 
apply (isweql2 Y Y (fun y:Y => (f (g y)))  (fun  y:Y => y)  efg' z (idisweq Y z)). 
apply (isweql1 _ _ g f egf z). assumption. 
Defined.
 


(** *** Some basic weak equivalences *)



Corollary isweqinvmap (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f): isweq _ _ (invmap _ _ f is).
Proof. intros. set (invf:= invmap _ _ f is). assert (efinvf: forall y:Y, paths _ (f (invf y)) y). apply weqfg. 
assert (einvff: forall x:X, paths _ (invf (f x)) x). apply weqgf. apply (gradth _ _  invf f efinvf einvff). Defined. 

Definition weqinv (X Y:UU): weq X Y -> weq Y X := fun u: weq X Y => weqpair _ _ (invmap _ _ (pr21 _ _ u) (pr22 _ _ u)) (isweqinvmap _ _ (pr21 _ _ u) (pr22 _ _ u)).

Corollary invinv (X Y :UU)(f:X -> Y)(is: isweq _ _ f): forall x:X, paths _  (invmap _ _ (invmap _ _ f is) (isweqinvmap _ _ f is) x) (f x).
Proof. intros. 
assert (e0: paths _ (f x) (invmap _ _ (invmap _ _ f is) (isweqinvmap _ _ f is) x)).
assert (e1: paths _ (invmap _ _ f is (f x)) x). apply (weqgf _ _ f is x).  apply pathsweq1. assumption.
apply pathsinv0. assumption. Defined.

Corollary isweqcontr2 (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr X -> iscontr Y.
Proof. intros. apply (iscontrxifiscontry _ _ (invmap _ _ f is1) (isweqinvmap _ _ f is1)). assumption. Defined.

Corollary isweqmaponpaths (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f)(x:X)(x':X): isweq _ _ (maponpaths _ _ f x x').
Proof. intros. apply (gradth _ _ (maponpaths _ _ f x x') (pathsweq2 _ _ f is x x') (pathsweq3 _ _ f is x x')  (pathsweq4 _ _ f is x x')). Defined.  


Corollary isweqpathsinv0 (X:UU)(x x':X): isweq _ _ (pathsinv0 _ x x').
Proof. intros.  apply (gradth _ _ (pathsinv0 _  x x') (pathsinv0 _ x' x) (pathsinv0inv0 _ _ _) (pathsinv0inv0 _ _ _)). Defined.


Corollary isweqpathscomp0r (X:UU)(x x' x'':X)(e': paths _ x' x''): isweq _ _ (fun e:paths _ x x' => pathscomp0 _ _ _ _ e e').
Proof. intros. set (f:= fun e:paths _ x x' => pathscomp0 _ _ _ _ e e'). set (g:= fun e'': paths _ x x'' => pathscomp0 _ _ _ _ e'' (pathsinv0 _ _ _ e')). 
assert (egf: forall e:_ , paths _ (g (f e)) e).   intro. destruct e.  simpl. destruct e'.  simpl.  apply idpath.
assert (efg: forall e'':_, paths _ (f (g e'')) e''). intro. destruct e''. simpl. destruct e'. simpl.   apply idpath. 
apply (gradth _ _ f g egf efg). Defined. 




Corollary  isweqfromcoconusf (X Y : UU)(f:X-> Y): isweq _ _ (fromcoconusf _ _ f).
Proof. intros. set (ff:= fromcoconusf _ _ f). set (gg:= tococonusf _ _ f).
assert (egf: forall yxe:_, paths _ (gg (ff yxe)) yxe). intro. destruct yxe.   destruct x. unfold gg. unfold tococonusf. unfold ff. unfold fromcoconusf.  simpl. destruct x. apply idpath.  
assert (efg: forall x:_, paths _ (ff (gg x)) x). intro. apply idpath.
apply (gradth _ _ _ _ egf efg). Defined.



Corollary isweqdeltap (T:UU) : isweq _ _ (deltap T).
Proof. intros. set (ff:=deltap T). set (gg:= fun z:pathsspace T => pr21 _ _ z). 
assert (egf: forall t:T, paths _ (gg (ff t)) t). intro. apply idpath.
assert (efg: forall tte: pathsspace T, paths _ (ff (gg tte)) tte). intro. destruct tte.  destruct x. destruct x. apply idpath. 
apply (gradth _ _ _ _ egf efg). Defined. 


Corollary isweqpr21pr21 (T:UU) : isweq (pathsspace' T) T (fun a:_ => (pr21 _ _ (pr21 _ _ a))).
Proof. intros. set (f:=  (fun a:_ => (pr21 _ _ (pr21 _ _ a))): pathsspace' T -> T). set (g:= (fun t:T => tpair _ _ (dirprodpair _ _ t t) (idpath _ t)): T -> pathsspace' T). 
assert (efg: forall t:T, paths _ (f (g t)) t). intro. apply idpath. 
assert (egf: forall a: pathsspace' T, paths _ (g (f a)) a). intro. destruct a.  destruct t. destruct x.   simpl. apply idpath. 
apply (gradth _ _ _ _ egf efg). Defined. 







(** *** The 2-out-of-3 property of weak equivalences.

Theorems showing that if any two of three functions f, g, gf are weak equivalences then so is the third - the 2-out-of-3 property. *)





Theorem twooutof3a (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z)(isgf: isweq _ _ (fun x:X => g(f x)))(isg: isweq _ _ g):isweq _ _ f.
Proof. intros. set (invg:= invmap _ _ g isg). set (invgf:= invmap _ _ (fun x:X => g(f x)) isgf). set (invf := (fun y:Y => invgf (g y))). 

assert (efinvf: forall y:Y, paths _ (f (invf y)) y). intro.   assert (int1: paths _ (g (f (invf y))) (g y)). unfold invf.  apply (weqfg _ _ (fun x:X => (g (f x))) isgf (g y)). apply (pathsweq2 _ _ g isg _ _ int1). 

assert (einvff: forall x: X, paths _ (invf (f x)) x). intro. unfold invf. apply (weqgf _ _ (fun x:X => (g (f x))) isgf x).

apply (gradth _ _ f invf einvff efinvf).  Defined.


Corollary ifcontrcontrthenweq (X:UU)(Y:UU)(f:X -> Y)(isx: iscontr X)(isy: iscontr Y): isweq _ _ f.
Proof. intros. set (py:= (fun y:Y => tt)). apply (twooutof3a _ _ _ f py (isweqcontrtounit X isx) (isweqcontrtounit Y isy)). Defined. 



Theorem twooutof3b (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z)(isf: isweq _ _ f)(isgf: isweq _ _ (fun x:X => g(f x))):isweq _ _ g.
Proof. intros. set (invf:= invmap _ _ f isf). set (invgf:= invmap _ _ (fun x:X => g(f x)) isgf). set (invg := (fun z:Z => f ( invgf z))). set (gf:= fun x:X => (g (f x))). 

assert (eginvg: forall z:Z, paths _ (g (invg z)) z). intro. apply (weqfg _ _ (fun x:X => (g (f x))) isgf z).  

assert (einvgg: forall y:Y, paths _ (invg (g y)) y). intro.  assert (isinvf: isweq _ _ invf). apply isweqinvmap.  assert (isinvgf: isweq _ _ invgf).  apply isweqinvmap. assert (int1: paths _ (g y) (gf (invf y))).  apply (maponpaths _ _ g _ _ (pathsinv0 _ _ _ (weqfg _ _ f isf y))). assert (int2: paths _ (gf (invgf (g y))) (gf (invf y))). assert (int3: paths _ (gf (invgf (g y))) (g y)). apply (weqfg _ _ gf isgf). induction int1. assumption. assert (int4: paths _ (invgf (g y)) (invf y)). apply (pathsweq2 _ _ gf isgf). assumption. assert (int5:paths _ (invf (f (invgf (g y)))) (invgf (g y))). apply (weqgf _ _ f isf). assert (int6: paths _ (invf (f (invgf (g (y))))) (invf y)).  induction int4. assumption. apply (pathsweq2 _ _ invf isinvf). assumption. apply (gradth _ _ g invg  einvgg eginvg). Defined.



Lemma isweql3 (X:UU)(Y:UU)(f:X-> Y)(g:Y->X)(egf: forall x:X, paths _ (g (f x)) x): isweq _ _ f -> isweq _ _ g.
Proof. intros. set (gf:= fun x:X => g (f x)). assert (int1: isweq _ _ gf). apply (isweqhomot _ _ (fun x:X => x) gf  (fun x:X => (pathsinv0 _ _ _ (egf x)))). apply idisweq.  apply (twooutof3b _ _ _ f g X0 int1). Defined. 

Theorem twooutof3c (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z)(isf: isweq _ _ f)(isg: isweq _ _ g):isweq _ _  (fun x:X => g(f x)).
Proof. intros. set (gf:= fun x:X => g (f x)). set (invf:= invmap _ _ f isf). set (invg:= invmap _ _ g isg). set (invgf:= fun z:Z => invf (invg z)). assert (egfinvgf: forall x:X, paths _ (invgf (gf x)) x). unfold gf. unfold invgf.  intro.  assert (int1: paths _ (invf (invg (g (f x))))  (invf (f x))). apply (maponpaths _ _ invf _ _ (weqgf _ _ g isg (f x))). assert (int2: paths _ (invf (f x)) x). apply weqgf.  induction int1. assumption. 
assert (einvgfgf: forall z:Z, paths _ (gf (invgf z)) z).  unfold gf. unfold invgf. intro. assert (int1: paths _ (g (f (invf (invg z)))) (g (invg z))). apply (maponpaths _ _ g _ _ (weqfg _ _ f isf (invg z))).   assert (int2: paths _ (g (invg z)) z). apply (weqfg _ _ g isg z). induction int1. assumption. apply (gradth _ _ gf invgf egfinvgf einvgfgf). Defined. 



Definition weqcomp (X Y Z:UU): (weq X Y) -> (weq Y Z) -> (weq X Z) := fun u: weq X Y => fun v: weq Y Z => weqpair _ _ (fun x:X => (pr21 _ _ v (pr21 _ _ u x))) (twooutof3c _ _ _ _ _ (pr22 _ _ u) (pr22 _ _ v)). 













(** * Basics about fibration sequences. *)



(** ** Fibrations sequences and their first "left shifts". *)

(** By a pre-fibration sequence we mean a structure of the form 
(X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(e: forall x:X, paths _ (g (f x)) z). Note that giving such a structure is essentially equivalent to giving a structure of the form (X Y Z:UU)(g:Y -> Z)(z:Z)(ezmap: X -> hfiber _ _ g z) where ezmap takes values of the form tpair i.e. values which are invariant under the would-be eta conversion for dependent sums. The mapping in one direction is given in the definition of ezmap below. The mapping in another is given by
 
f:= fun x:X => pr21 _ _ (ezmap x)
ez: fun x:X => pr22 _ _ (ezmap x).

A pre-fibration sequence is called a fibration sequence if ezmap is a weak equivalence. We construct for any fibration sequence X -> Y -> (Z,z) its derived seqiuences  paths _ (g y) z -> X -> (Y,y) and identify the first function in the second derived sequence paths _ (f x) y -> paths _ (g y) z -> (X,x) 


*)


Definition ezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z) : X -> hfiber _ _ g z := 
fun x:X => hfiberpair _ _ g z (f x) (ez x).

Definition isfibseq (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z) := isweq _ _ (ezmap _ _ _ f g z ez). 


Definition diff1invezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(y:Y) : hfiber _ _ f y -> paths _ (g y) z :=  
fun xe: hfiber _ _ f y =>
match xe with
tpair x e => pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ _ e)) (ez x)
end.



Lemma diaglemma1 (Y Z:UU)(g:Y -> Z)(y y':Y)(z:Z)(phi: paths _ y' y)(ee: paths _ (g y) z)(ee': paths _ (g y') z) (e1: paths _ ee' (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ phi) ee)): paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ _ phi)) ee') ee.
Proof. intros. induction phi. simpl. simpl in e1. assumption. Defined.



Lemma isweqdiff1invezmap  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y): isweq _ _ (diff1invezmap _ _ _ f g z ez y).
Proof. intros. set (ff:= diff1invezmap _ _ _ f g z ez y). set (ezm:= ezmap _ _ _ f g z ez). set (invezm:= invmap _ _ (ezmap _ _ _ f g z ez) is). set (pr21y:= pr21 Y (fun y:Y => paths _ (g y) z)).
set (gg:= fun ee:paths _ (g y) z => hfiberpair _ _ f y (invezm (hfiberpair _ _ g z y ee)) (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y ee)))). 

assert (efg: forall ee:paths _ (g y) z, paths _ (ff (gg ee)) ee). intro.
assert (e1: paths _ (pr22 _ _ (ezm (invezm (hfiberpair _ _ g z y ee)))) (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y ee)))) ee)). apply (hfibertriangle1 _ _ g z _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y ee))).
apply (diaglemma1 _ _ g y (f (invezm (hfiberpair _ _ g z y ee))) z (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y ee))) ee (pr22 _ _ (ezm (invezm (hfiberpair _ _ g z y ee)))) e1). 

assert (egf: forall yee: hfiber _ _ f y, paths _ (gg (ff yee)) yee). intro.  induction yee. induction x. simpl. rename t into x.
set (e:=weqgf _ _ ezm is x).
assert (ee: paths _ (pr22 _ _ (gg (ez x))) (maponpaths _ _ f _ _ (weqgf _ _ ezm is x))).
assert (e2: paths _ (pr22 _ _ (gg (ez x))) (maponpaths _ _ pr21y _ _ (maponpaths _ _ ezm _ _ (weqgf _ _ ezm is x)))).
assert (e3: paths _ (pr22 _ _ (gg (ez x))) (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (ezm x)))). simpl. apply idpath.
assert (e4: paths _ (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (ezm x))) (maponpaths _ _ pr21y _ _ (maponpaths _ _ ezm _ _ (weqgf _ _ ezm is x)))). 
assert (e5: paths _ (weqfg _ _ ezm is (ezm x))  (maponpaths _ _ ezm _ _ (weqgf _ _ ezm is x))). apply (pathsinv0 _ _ _ (weqfgf _ _ ezm is x)).
apply (maponpaths _ _ (fun e:_ => maponpaths _ _ pr21y _ _ e) _ _ e5).  assumption. 
assert (e6: paths _ (maponpaths _ _ pr21y _ _ (maponpaths _ _ ezm _ _ (weqgf _ _ ezm is x))) (maponpaths _ _ f _ _ (weqgf _ _ ezm is x))). apply 
(maponpathsfuncomp _ _ _ ezm pr21y _ _ (weqgf _ _ ezm is x)).
apply (pathscomp0 _ _ _ _ e2 e6). 
assert (eee: paths _ (pr22 _ _ (gg (ez x))) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (weqgf _ _ ezm is x)) (idpath _ (f x)))). apply (pathscomp0 _ _ _ _ ee (pathsinv0 _ _ _ (pathscomp0rid _ _ _ (maponpaths _ _ f _ _ (weqgf _ _ ezm is x))))). 
apply (hfibertriangle2 _ _ f (f x) (gg (ez x)) (hfiberpair _ _ f (f x) x (idpath _ (f x))) e eee). 
apply (gradth _ _ ff gg egf efg). Defined.



Definition diff1ezmap  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y) : paths _ (g y) z -> hfiber _ _ f y := fun e: paths _ (g y) z => 
hfiberpair _ _ _ _ (pr21 _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e))  (pr22 _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e)).


Definition diff1f  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(e: paths _ (g y) z): X := pr21 _ _ (diff1ezmap _ _ _ f g z ez is y e).

Definition diff1ez  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(e: paths _ (g y) z): paths _ (f (diff1f _ _ _ f g z ez is y e)) y:= pr22 _ _ (diff1ezmap _ _ _ f g z ez is y e).


Theorem isfibseqdiff1 (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y) : isfibseq _ _ _  (diff1f _ _ _ f g z ez is y) f y (diff1ez _ _ _ f g z ez is y).
Proof. intros.  unfold isfibseq. 
assert (is1: isweq _ _ (diff1ezmap _ _ _ f g z ez is y)).
assert (is2: isweq _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y))).  apply (isweqinvmap _ _  (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y)). 
assert (homot0: forall e: paths _ (g y) z, paths _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e) (diff1ezmap _ _ _ f g z ez is y e)). intro. apply (tppr _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e)). apply (isweqhomot _ _ _ _ homot0 is2). assumption. Defined.


Lemma fibseqhomot1 (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y) (e: paths _ (g y) z): paths _ (diff1f _ _ _ f g z ez is y e) (invmap _ _ (ezmap _ _ _ f g z ez) is (tpair _ _ y e)).
Proof. intros.  set (inv:= diff1invezmap _ _ _ f g z ez y). set (map1:= diff1ezmap _ _ _ f g z ez is y). set (map2:= fun e: paths _ (g y) z => hfiberpair _ _ g z y e). 

assert (e0: forall xe: hfiber _ _ f y, paths _ (ezmap _ _ _ f g z ez (pr21 _ _ xe)) (map2 (inv xe))). intro.  induction xe. simpl. unfold map2.   unfold ezmap. simpl. induction x.  simpl.  apply idpath.  
assert (e1: paths _ (inv (map1 e)) e). apply (weqgf _ _ map1 (isfibseqdiff1 _ _ _ f g z ez is y) e).
assert (e2: paths _ (map2 (inv (map1 e))) (map2 e)). apply (maponpaths _ _ map2 _ _ e1).
assert (e3: paths _  (ezmap _ _ _ f g z ez (pr21 _ _ (map1 e)))  (map2 (inv (map1 e)))). apply (e0 (map1 e)).
assert (e4: paths _  (ezmap _ _ _ f g z ez (pr21 _ _ (map1 e))) (map2 e)).  apply (pathscomp0 _ _ _ _ e3 e2). 
apply (pathsweq1 _ _ (ezmap _ _ _ f g z ez) is (pr21 _ _ (map1 e)) (map2 e)). assumption. Defined. 



Definition diff2ezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X) :  paths _ (f x) y -> hfiber _ _ (diff1f _ _ _ f g z ez is y) x := diff1ezmap _ _ _ (diff1f _ _ _ f g z ez is y) f y (diff1ez _ _ _ f g z ez is y) (isfibseqdiff1 _ _ _ f g z ez is y) x.


Definition diff2f (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X) : paths _ (f x) y -> paths _ (g y) z := (fun e:_ => pr21 _ _ (diff2ezmap _ _ _ f g z ez is y x e)).


Definition diff2ez (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X)(e: paths _ (f x) y): paths _ (diff1f _ _ _ f g z ez is y (diff2f _ _ _ f g z ez is y x e)) x :=  pr22 _ _ (diff2ezmap _ _ _ f g z ez is y x e).







Theorem fibseqhomot2  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X): forall e: paths _ (f x) y, paths _ (diff2f _ _ _ f g z ez is y x e) (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ _ e)) (ez x)).
Proof. intros.  
assert (e1: paths _ (diff2f _ _ _ f g z ez is y x e) (invmap _ _ (diff1ezmap _ _ _ f g z ez is y) (isfibseqdiff1 _ _ _ f g z ez is y) (tpair _ _ x e))). apply (fibseqhomot1).
assert (e2: forall xe:_ , paths _  (invmap _ _ (diff1ezmap _ _ _ f g z ez is y) (isfibseqdiff1 _ _ _ f g z ez is y) xe) (diff1invezmap _ _ _ f g z ez y xe)). apply (invinv _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y)). set (e3:= e2 (tpair _ _ x e)).   apply (pathscomp0 _ _ _ _ e1 e3). Defined.


(** ** The first four fibration sequences associated with a function. *)


Definition d1f (X Y:UU)(f:X -> Y)(y:Y): hfiber _ _ f y -> X := pr21 _ _.

Theorem isfibseq1 (X Y:UU)(f:X -> Y)(y:Y) : isfibseq _ _ _ (d1f _ _ f y) f y (fun xe: _ => pr22 _ _ xe).
Proof. intros. assert (forall xe': hfiber _ _ f y, paths _ xe' (ezmap  _ _ _ (d1f _ _ f y) f y (fun xe: _ => pr22 _ _ xe) xe')). intro. apply tppr. apply (isweqhomot _ _ _ _ X0 (idisweq _)).  Defined.


Definition d2f  (X Y:UU)(f:X -> Y)(y:Y)(x:X): paths _ (f x) y -> hfiber _ _ f y := hfiberpair _ _ f y x.


Theorem isfibseq2  (X Y:UU)(f:X -> Y)(y:Y)(x:X): isfibseq _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun e:_ => idpath _ _).
Proof. intros.  apply (isfibseqdiff1 _ _ _ (d1f _ _ f y) f y  (fun xe: _ => pr22 _ _ xe) (isfibseq1 _ _ f y) x). Defined.


Definition d3f (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y): paths _ (pr21 _ _ xe') x -> paths _ (f x) y:= diff2f _ _ _ (d1f _ _ f y) f y (fun xe: _ => pr22 _ _ xe) (isfibseq1 _ _ f y) x xe'. 

Lemma d3fhomot  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (pr21 _ _ xe') x) : paths _ (d3f _ _ f y x xe' e) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ e)) (pr22 _ _ xe')).
Proof. intros. apply fibseqhomot2. Defined.


Definition d3fez  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y): forall e: paths _ (pr21 _ _ xe') x, paths _ (d2f _ _ f y x (d3f _ _ f y x xe' e)) xe':= diff2ez _ _ _ (d1f _ _ f y) f y (fun xe: _ => pr22 _ _ xe) (isfibseq1 _ _ f y) x xe'. 

Theorem isfibseq3 (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y): isfibseq _ _ _ (d3f _ _ f y x xe') (d2f _ _ f y x) xe' (d3fez _ _ f y x xe').
Proof. intros. unfold isfibseq. apply isfibseqdiff1. Defined.



Definition d4f (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e:paths _ (f x) y): paths _ (hfiberpair _ _ f y x e) xe' -> paths _ (pr21 _ _ xe') x := diff2f _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe: _ => idpath _ _) (isfibseq2 _ _ f y x) xe' e. 

 

Lemma d4fhomot  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y)(ee: paths _ (hfiberpair _ _ f y x e) xe') : paths _ (d4f _ _ f y x xe' e ee) (maponpaths _ _ (pr21 _ _) _ _ (pathsinv0 _ _ _ ee)).
Proof. intros. 
assert (e1: paths (paths X (d1f X Y f y xe') x)
    (diff2f (paths Y (f x) y) (hfiber X Y f y) X (d2f X Y f y x)
       (d1f X Y f y) x
       (fun xe : paths Y (f x) y => idpath X (d1f X Y f y (d2f X Y f y x xe)))
       (isfibseq2 X Y f y x) xe' e ee)
    (pathscomp0 X (d1f X Y f y xe') (d1f X Y f y (d2f X Y f y x e)) x
       (maponpaths (hfiber X Y f y) X (d1f X Y f y) xe' 
          (d2f X Y f y x e)
          (pathsinv0 (hfiber X Y f y) (d2f X Y f y x e) xe' ee))
       (idpath X (d1f X Y f y (d2f X Y f y x e))))). apply (fibseqhomot2 _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe: _ => idpath _ _) (isfibseq2 _ _ f y x) xe' e ee).  
assert (e2: paths _ (pathscomp0 X (d1f X Y f y xe') (d1f X Y f y (d2f X Y f y x e)) x
            (maponpaths (hfiber X Y f y) X (d1f X Y f y) xe'
               (d2f X Y f y x e)
               (pathsinv0 (hfiber X Y f y) (d2f X Y f y x e) xe' ee))
            (idpath X (d1f X Y f y (d2f X Y f y x e)))) (maponpaths (total2 X (fun pointover : X => paths Y (f pointover) y)) X
        (pr21 X (fun pointover : X => paths Y (f pointover) y)) xe'
        (hfiberpair X Y f y x e)
        (pathsinv0 (hfiber X Y f y) (hfiberpair X Y f y x e) xe' ee))). apply pathscomp0rid.
apply (pathscomp0 _ _ _ _ e1 e2). Defined.


Definition d4fez  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y): forall ee: paths _ (hfiberpair _ _ f y x e) xe', paths _ (d3f _ _ f y x xe' (d4f _ _ f y x xe' e ee)) e:= diff2ez _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe: _ => idpath _ _) (isfibseq2 _ _ f y x) xe' e. 

Theorem isfibseq4 (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y): isfibseq _ _ _ (d4f _ _ f y x xe' e) (d3f _ _ f y x xe') e (d4fez _ _ f y x xe' e).
Proof. intros. unfold isfibseq. apply isfibseqdiff1. Defined.






(** ** Homotopy fibers of the projection [pr21 T P: total2 T P -> T]. 


Theorems saying that for T:UU and P:T -> UU the homotopy fiber of the projection total2 T P -> T over t:T is weakly equivalent to P t. *)




Definition fibmap1 (T:UU) (P:T-> UU) (t:T): P t -> (hfiber _ _ (pr21 T P) t) := (fun z: P t => tpair _ _ (tpair T P t z) (idpath T t)).

Definition fibmap2 (T:UU) (P:T-> UU) (t:T): (hfiber _ _ (pr21 T P) t) -> P t:= fun z: hfiber  _ _ (pr21 T P) t =>
match z with 
tpair zz e => (transportf T P  (pr21 _ _ zz) t e (pr22 T P zz))
end.



Theorem isweqfibmap1 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap1 T P t).
Proof. intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _ (fibmap1 T P t) (fibmap2 T P t) e1 e2). Defined. 

Theorem isweqfibmap2 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap2 T P t).
Proof.  intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _  (fibmap2 T P t) (fibmap1 T P t) e2 e1). Defined. 



Corollary trivfib1 (T:UU) (P:T -> UU) (is1: forall t:T, iscontr (P t)) : isweq _ _ (pr21 T P).
Proof. intros. unfold isweq.  intro. set (isy:= is1 y). apply (iscontrxifiscontry _ _ (fibmap2 T P y) (isweqfibmap2 T P y)). assumption. Defined. 



Corollary familyfibseq (T:UU)(P:T->UU)(t:T): isfibseq (P t) (total2 T P) T (fun p: P t => tpair _ _ t p) (pr21 T P) t (fun p: P t => idpath _ t).
Proof. intros. unfold isfibseq. unfold ezmap.  apply isweqfibmap1. Defined.






(** ** Construction of the fibration sequence defined by a composable pair of functions

(hfiber f) -> (hfiber gf) -> (hfiber g)


*)


Section hfibersseq.

Variables X Y Z: UU.
Variable f:X->Y.
Variable g:Y->Z.
Variable z:Z.
Variable ye: hfiber _ _ g z.

Let gf:= fun x:X => g (f x).
Let y:=pr21 _ _ ye.
Let e:=pr22 _ _ ye. 




Definition hfibersinvezmap : hfiber _ _ (hfibersgftog _ _ _ f g z) ye ->  hfiber _ _ f y.
Proof. intros. destruct X0. rename x into e0. destruct t. rename x into e'. rename t into x.  set (prg:= (fun z: (hfiber Y Z g z) => pr21 _ _ z)). set (int:= hfiberpair _ _ f y  x (maponpaths _ _ prg _ _ e0)). assumption. Defined.  


Definition hfiberpath1 (y1:Y)(e1: paths _ (g y1) z)(y2:Y)(e21:paths _ y2 y1): paths _ (hfiberpair _ _  g z y2 (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ e21) e1)) (hfiberpair _ _ g z y1 e1).
Proof. intros.  induction e21. simpl. apply idpath. Defined.  

Definition hfiberpath11 (y1:Y)(e1: paths _ (g y1) z)(y2:Y)(e21:paths _ y2 y1): paths _ (maponpaths _ _ (fun u: hfiber _ _ g z => pr21 _ _ u) _ _ (hfiberpath1 y1 e1 y2 e21)) e21.
Proof. intros.  simpl. induction e21. simpl. apply idpath. Defined. 

Definition gzx: UU := total2 (hfiber _ _ g z) (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))). 



Definition gzxmap3: hfiber _ _ f y -> hfiber _ _ (fun t: gzx => pr21 _ _ t) ye.
Proof. intros.  set (int1:= tpair _  (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))) ye X0). split with int1. simpl. apply idpath. Defined.

Definition gzxmap4: hfiber _ _ (fun t: gzx  => pr21 _ _ t) ye -> hfiber _ _ f y.
Proof. intros. destruct X0. rename x into e4. destruct t.  destruct x. destruct t.  simpl in e4. simpl in x.  rename x into e2. rename t0 into x. rename t into y'. rename x0 into e1. set (ee0:= maponpaths _ _ (fun z: hfiber _ _ g z => pr21 _ _ z) _ _ e4).  set (ee:= pathscomp0 _ _ _ _ e2 ee0). simpl in ee. apply (hfiberpair _ _ f y x ee). Defined.
 


Definition gzxmap1  : hfiber _ _ (hfibersgftog _ _ _ f g z) ye -> hfiber _ _ (fun t: gzx => pr21 _ _ t) ye.
Proof. intros. destruct X0.  destruct t. rename x into e0. rename x0 into e'. rename t into x. set (int1:= tpair (hfiber _ _ g z) (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))) (hfiberpair _ _ g z (f x) e') (hfiberpair _ _ f  (f x) x (idpath _ (f x)))). split with int1. simpl. assumption. Defined. 


Definition gzxmap2 : hfiber _ _ (fun t: gzx => pr21 _ _ t) ye ->  hfiber _ _ (hfibersgftog _ _ _ f g z) ye.
Proof. intros. destruct X0. destruct t. destruct x0. destruct t. rename x1 into e1. rename t into y'. rename x into e4. rename t0 into x. simpl in x0. rename x0 into e2. simpl in e4. set (int1:= hfiberpair _ _ (fun x0 : X => g (f x0)) z x (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ e2) e1)).  split with int1. simpl. assert (e5: paths _  (hfiberpair Y Z g z (f x) (pathscomp0 Z (g (f x)) (g y') z (maponpaths Y Z g (f x) y' e2) e1)) (tpair Y (fun pointover : Y => paths Z (g pointover) z) y' e1)). apply hfiberpath1. apply (pathscomp0 _ _ _ _ e5 e4). Defined. 





Definition gzxhom412  (t: hfiber _ _ (fun t: gzx => pr21 _ _ t) ye): paths _ (gzxmap4  (gzxmap1 (gzxmap2  t))) (gzxmap4 t).
Proof. intros.  destruct t. destruct t. destruct t. destruct x0. simpl. simpl in x. rename x into e4. simpl in x0. rename x0 into e2. rename t into y'. rename t0 into x. rename x1 into e1.
assert (int1: paths _ (maponpaths (hfiber Y Z g z) Y
           (fun z0 : hfiber Y Z g z =>
            pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
           (tpair Y (fun pointover : Y => paths Z (g pointover) z) 
              (f x)
              (pathscomp0 Z (g (f x)) (g y') z (maponpaths Y Z g (f x) y' e2)
                 e1)) ye
           (pathscomp0 (hfiber Y Z g z)
              (hfiberpair Y Z g z (f x)
                 (pathscomp0 Z (g (f x)) (g y') z
                    (maponpaths Y Z g (f x) y' e2) e1))
              (tpair Y (fun pointover : Y => paths Z (g pointover) z) y' e1)
              ye (hfiberpath1 y' e1 (f x) e2)
              e4)) (pathscomp0 _ _ _ _ (maponpaths _ _  (fun z0 : hfiber Y Z g z =>
            pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0) _ _ (hfiberpath1 y' e1 (f x) e2)) (maponpaths _ _  (fun z0 : hfiber Y Z g z =>
            pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0) _ _ e4))).    apply maponpathscomp0. simpl in int1. assert (int2: paths _  (pathscomp0 Y (f x) y' y
              (maponpaths (hfiber Y Z g z) Y
                 (fun z0 : hfiber Y Z g z =>
                  pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
                 (hfiberpair Y Z g z (f x)
                    (pathscomp0 Z (g (f x)) (g y') z
                       (maponpaths Y Z g (f x) y' e2) e1))
                 (hfiberpair Y Z g z y' e1)
                 (hfiberpath1 y' e1 (f x) e2))
              (maponpaths (hfiber Y Z g z) Y
                 (fun z0 : hfiber Y Z g z =>
                  pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
                 (tpair Y (fun pointover : Y => paths Z (g pointover) z) y'
                    e1) ye e4))

        (pathscomp0 Y (f x) y' y e2
           (maponpaths (hfiber Y Z g z) Y
              (fun z0 : hfiber Y Z g z =>
               pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
              (tpair Y (fun pointover : Y => paths Z (g pointover) z) y' e1)
              ye e4))).

assert (int3: paths _ (maponpaths (hfiber Y Z g z) Y
           (fun z0 : hfiber Y Z g z =>
            pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
           (hfiberpair Y Z g z (f x)
              (pathscomp0 Z (g (f x)) (g y') z (maponpaths Y Z g (f x) y' e2)
                 e1)) (hfiberpair Y Z g z y' e1)
           (hfiberpath1 y' e1 (f x) e2)) e2).  simpl.
apply (hfiberpath11 y' e1 (f x) e2). simpl in int3. 
apply pathscomp021.  assumption. 

assert (int5: paths _ (maponpaths (hfiber Y Z g z) Y
           (fun z0 : hfiber Y Z g z =>
            pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
           (tpair Y (fun pointover : Y => paths Z (g pointover) z) 
              (f x)
              (pathscomp0 Z (g (f x)) (g y') z (maponpaths Y Z g (f x) y' e2)
                 e1)) ye
           (pathscomp0 (hfiber Y Z g z)
              (hfiberpair Y Z g z (f x)
                 (pathscomp0 Z (g (f x)) (g y') z
                    (maponpaths Y Z g (f x) y' e2) e1))
              (tpair Y (fun pointover : Y => paths Z (g pointover) z) y' e1)
              ye (hfiberpath1 y' e1 (f x) e2)
              e4))

(pathscomp0 Y (f x) y' y e2
           (maponpaths (hfiber Y Z g z) Y
              (fun z0 : hfiber Y Z g z =>
               pr21 Y (fun pointover : Y => paths Z (g pointover) z) z0)
              (tpair Y (fun pointover : Y => paths Z (g pointover) z) y' e1)
              ye e4))). simpl. apply (pathscomp0 _ _ _ _ int1 int2). 

simpl in int5. apply (maponpaths _ _ (fun eee: paths Y (f x) y => hfiberpair _ _ f y x eee) _ _ int5). Defined. 


Lemma isweqgzxmap4l1  (u: hfiber _ _ f y):
 paths _ (gzxmap4  (fibmap1 _ (fun v: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ v))) ye u)) u.  
Proof. intros. destruct u.   simpl. destruct ye.  assert (int: paths _ (pathscomp0 Y (f t) y y x (idpath Y y)) x). apply pathscomp0rid.   apply (maponpaths _ _ (fun ee: (paths Y (f t) y) => hfiberpair _ _ f y t ee) _ _ int).  Defined. 

Lemma  isweqgzxmap4 : isweq _ _ gzxmap4.
Proof. intros. set (h:=fibmap1 _ (fun ye: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ ye))) ye). simpl in h. assert (int1: isweq _ _ h). apply (isweqfibmap1  _ (fun ye: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ ye))) ye).  apply (isweql3 _ _  h gzxmap4 (isweqgzxmap4l1) int1). Defined. 



Definition gzxhom12   (t: hfiber _ _ (fun t: gzx  => pr21 _ _ t) ye): paths _ (gzxmap1  (gzxmap2  t)) t. 
Proof. intros. assert (int1: paths _ (gzxmap4  (gzxmap1 (gzxmap2 t))) (gzxmap4 t)). apply gzxhom412. apply  (pathsweq2 _ _ (gzxmap4) (isweqgzxmap4 ) _ _ int1). Defined. 


Definition gzxhom21  (t:hfiber _ _ (hfibersgftog _ _ _ f g z) ye) : paths _ (gzxmap2 (gzxmap1 t)) t. 
Proof. intros. destruct t.  destruct t. simpl. apply idpath. Defined. 


Lemma isweqgzxmap1  : isweq _ _ gzxmap1 .
Proof. intros. apply (gradth _  _ gzxmap1  gzxmap2  gzxhom21 gzxhom12 ).  Defined. 


Definition fibseqhom (u: hfiber _ _ (hfibersgftog _ _ _ f g z) ye): paths _ (gzxmap4 (gzxmap1  u)) (hfibersinvezmap  u).
Proof. intros. destruct u.   destruct t. simpl. apply idpath. Defined. 


Theorem isweqhfibersinvezmap : isweq _ _ hfibersinvezmap.
Proof.  intros. set (int1:= (fun u: hfiber _ _ (hfibersgftog _ _ _ f g z) ye => (gzxmap4  (gzxmap1  u)))). assert (isweq _ _ int1). apply (twooutof3c _ _ _ gzxmap1  gzxmap4 isweqgzxmap1 isweqgzxmap4). apply (isweqhomot _ _ int1 hfibersinvezmap fibseqhom X0). Defined.


Definition hfibersezmap: hfiber _ _ f y -> hfiber _ _ (hfibersgftog _ _ _ f g z) ye := fun xe:_ => tpair _ _ (pr21 _ _ (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe)) (pr22 _ _ (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe)).

Lemma isweqhfibersezmap: isweq _ _ hfibersezmap.
Proof. assert (homot: forall xe: _ , paths _  (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe) (hfibersezmap xe)). intro. apply (tppr _ _ _).  apply (isweqhomot _ _ _ _ homot (isweqinvmap _ _ hfibersinvezmap isweqhfibersinvezmap)). Defined.


End hfibersseq. 



(** Main corollaries of the constructions of hfibersseq. *)


Corollary isweqhfibersgftog (X:UU)(Y:UU)(Z:UU)(f:X -> Y)(g:Y -> Z)(z:Z):(isweq _ _ f) -> (isweq _ _ (hfibersgftog _ _ _ f g z)).
Proof. intros. unfold isweq.   intro. set (u:= hfibersinvezmap X Y Z f g z y). assert (is1: isweq _ _ u). apply isweqhfibersinvezmap.  assert (int: iscontr (hfiber X Y f (pr21 Y (fun pointover : Y => paths Z (g pointover) z) y))). apply X0.  apply (iscontrxifiscontry _ _ u is1 int). Defined.


Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)):  hfiber _ _ (fun x:X => g (f x)) z:= pr21 _ _ (hfibersezmap _ _ _ f g z ye xe). 


Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)): paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye := pr22 _ _ (hfibersezmap _ _ _ f g z ye xe).



(** There are the follwing alternative definitions of hfibersftogf and hfibseqez:

Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z): hfiber _ _ f (pr21 _ _ ye) -> hfiber _ _ (fun x:X => g (f x)) z:= fun xe:_ => hfiberpair _ _ (fun x:X => g (f x)) z (pr21 _ _ xe) (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye)).


Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)): paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye := hfibertriangle2 _ _ g z (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye (pr22 _ _ xe) (idpath _ (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye))).

However I do not know whether the are equivalent to the ones given below or whether one can prove that the resulting pre-fibration sequence is a fibration sequence. *)


Corollary isfibseqhfibers (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z): isfibseq (hfiber _ _ f (pr21 _ _ ye)) (hfiber _ _ (fun x:X => g (f x)) z) (hfiber _ _ g z)  (hfibersftogf _ _ _ f g z ye) (hfibersgftog _ _ _ f g z) ye (hfibersez _ _ _ f g z ye).
Proof. intros.  unfold isfibseq. apply isweqhfibersezmap. Defined.













(** ** Fiber-wise weak equivalences. 


Theorems saying that a fiber-wise morphism between total spaces is a weak equivalence if and only if all the morphisms between the fibers are weak equivalences. *)


Definition totalfun (X:UU)(P:X-> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x) := (fun z: total2 X P => tpair X Q (pr21 _ _ z) (f (pr21 _ _ z) (pr22 _ _ z))).


Theorem isweqtotaltofib (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
isweq _ _ (totalfun _ _ _ f) -> forall x:X, isweq _ _ (f x).
Proof. intros. set (totp:= total2 X P). set (totq := total2 X Q).  set (totf:= (totalfun _ _ _ f)). set (pip:= fun z: totp => pr21 _ _ z). set (piq:= fun z: totq => pr21 _ _ z). 

set (hfx:= hfibersgftog _ _ _ totf piq x).  simpl in hfx. 
assert (isweq _ _ hfx). unfold isweq. intro. 
set (int:=hfibersinvezmap _ _ _ totf piq x y). assert (isweq _ _ int). apply (isweqhfibersinvezmap _ _ _ totf piq x y). destruct y. assert (is1: iscontr (hfiber _ _ totf t)). apply (X0 t). apply (iscontrxifiscontry _ _ int X1 is1).   
set (ip:= fibmap1 X P x). set (iq:= fibmap1 X Q x). set (h:= fun p: P x => hfx (ip p)).  assert (is2: isweq _ _ h). apply (twooutof3c _ _ _ ip hfx (isweqfibmap1 X P x) X1). set (h':= fun p: P x => iq ((f x) p)). assert (ee: forall p:P x, paths _ (h p) (h' p)). intro. apply idpath.  assert (isweq _ _ h'). apply (isweqhomot  _ _ h h' ee is2). apply (twooutof3a _ _ _ (f x) iq X2). apply (isweqfibmap1 X Q x). Defined.
 

Theorem isweqfibtototal (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
(forall x:X, isweq _ _ (f x)) -> isweq _ _ (totalfun _ _ _ f).
Proof. intros. set (fpq:= totalfun _ _ _ f). set (pr21p:= fun z: total2 X P => pr21 _ _ z). set (pr21q:= fun z: total2 X Q => pr21 _ _ z). unfold isweq. intro.  rename y into xq.  set (x:= pr21q xq). set (xqe:= hfiberpair _ _ pr21q x xq (idpath _ _)). set (hfpqx:= hfibersgftog _ _ _ fpq pr21q x). 

assert (isint: iscontr (hfiber _ _ hfpqx xqe)). assert (isint1: isweq _ _ hfpqx). set (ipx:= fibmap1 X P x). set (iqx:= fibmap1 X Q x).   set (diag:= fun p:P x => (iqx ((f x) p))). assert (is2: isweq _ _ diag).  apply (twooutof3c _ _ _ (f x) iqx (X0 x) (isweqfibmap1 X Q x)).  apply (twooutof3b _ _ _ ipx hfpqx (isweqfibmap1 X P x) is2).  unfold isweq in isint1.  apply (isint1 xqe). 
set (intmap:= hfibersinvezmap _ _ _ fpq pr21q x xqe). apply (isweqcontr2 _ _ intmap (isweqhfibersinvezmap _ _ _ fpq pr21q x xqe) isint). 
Defined.








(** ** Homotopy fibers of the function [fpmap: total2 X (P f) -> total2 Y P].

Given X Y in UU, P:Y -> UU and f: X -> Y we get a function fpmap: total2 X (P f) -> total2 Y P. The main theorem of this section asserts that the homotopy fiber of fpmap over yp:total Y P is naturally weakly equivalent to the homotopy fiber of f over pr21 yp. In particular, if f is a weak equivalence then so is fpmap. *)


Definition fpmap (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU) : total2 X (fun x:X => P (f x)) -> total2 Y P := 
(fun z:total2 X (fun x:X => P (f x)) => tpair Y P (f (pr21 _ _ z)) (pr22 _ _ z)).


Definition hffpmap2 (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU):  total2 X (fun x:X => P (f x)) -> total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)).
Proof. intros. set (u:= fpmap _ _ f P X0).  split with u. set (x:= pr21 _ _ X0).  split with x. simpl. apply idpath. Defined.


Definition hfiberfpmap (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): hfiber _ _ (fpmap _ _ f P) yp -> hfiber _ _ f (pr21 _ _ yp).
Proof. intros. set (int1:= hfibersgftog _ _ _ (hffpmap2 _ _ f P) (fun u: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => (pr21 _ _ u)) yp).  set (phi:= fibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). apply (phi (int1 X0)).   Defined. 



Lemma centralfiber (X:UU)(P:X -> UU)(x:X): isweq _ _ (fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p).
Proof. intros. set (f:= fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p). set (g:= fun z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) => transportf X P (pr21 _ _ (pr21 _ _ z)) x (pathsinv0 _ _ _ (pr22 _ _ (pr21 _ _ z))) (pr22 _ _ z)).  

assert (efg: forall  z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)), paths _ (f (g z)) z). intro. destruct z. destruct t.   simpl. induction x1. simpl. apply idpath. 

assert (egf: forall p: P x , paths _ (g (f p)) p).  intro. apply idpath.  

apply (gradth _ _  f g egf efg). Defined. 


Lemma isweqhff (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU): isweq _ _ (hffpmap2 _ _ f P). 
Proof. intros. set (int:= total2 X (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)))). set (intpair:= tpair X (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)))).  set (toint:= fun z: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => intpair (pr21 _ _ (pr22 _ _ z)) (tpair _  (fun u: coconusfromt _ (f (pr21 _ _ (pr22 _ _ z))) => P (pr21 _ _ u)) (coconusfromtpair _ _ (pr21 _ _ (pr21 _ _ z)) (pr22 _ _ (pr22 _ _ z))) (pr22 _ _ (pr21 _ _ z)))). set (fromint:= fun z: int => tpair _ (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) (tpair Y P (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr22 _ _ (pr22 _ _ z))) (hfiberpair _ _ f (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr21 _ _ z) (pr22 _ _ (pr21 _ _ (pr22 _ _ z))))). assert (fromto: forall u:(total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))), paths _ (fromint (toint u)) u). simpl in toint. simpl in fromint. simpl. intro. destruct u. destruct x. destruct t. simpl. unfold toint. unfold fromint. simpl. apply idpath. assert (tofrom: forall u:int, paths _ (toint (fromint u)) u). intro. destruct u. destruct x. destruct t0. simpl in x. simpl. unfold fromint. unfold toint. simpl. apply idpath. assert (is: isweq _ _ toint). apply (gradth _ _ toint fromint fromto tofrom).  clear tofrom. clear fromto.  clear fromint.

set (h:= fun u: total2 X (fun x:X => P (f x)) => toint ((hffpmap2 _ _ f P) u)). simpl in h. 

assert (l1: forall x:X, isweq _ _ (fun p: P (f x) => tpair _  (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)) (coconusfromtpair _ _ (f x) (idpath _  (f x))) p)). intro. apply (centralfiber Y P (f x)).  

assert (isweq _ _ h). apply (isweqfibtototal X (fun x:X => P (f x))  (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u))) (fun x:X => (fun p: P (f x) => tpair _  (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)) (coconusfromtpair _ _ (f x) (idpath _  (f x))) p))). assumption.   

apply (twooutof3a _ _ _ (hffpmap2 _ _ f P) toint X0 is). Defined. 




Theorem isweqhfiberfp (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): isweq _ _ (hfiberfpmap _ _ f P yp).
Proof. intros. set (int1:= hfibersgftog _ _ _ (hffpmap2 _ _ f P) (fun u: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => (pr21 _ _ u)) yp). assert (is1: isweq _ _ int1). apply isweqhfibersgftog. apply isweqhff. set (phi:= fibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). assert (is2: isweq _ _ phi). apply (isweqfibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). apply (twooutof3c _ _ _ int1 phi is1 is2).   Defined. 


Corollary isweqfpmap (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU): isweq _ _ f -> isweq _ _ (fpmap _ _ f P).
Proof. intros. unfold isweq.   intro. unfold isweq in X0.  set (h:=hfiberfpmap _ _ f P y). assert (isweq _ _ h). apply isweqhfiberfp. assert (is: iscontr (hfiber X Y f (pr21 _ _ y))). apply X0. apply (iscontrxifiscontry _ _  h X1 is). Defined. 




(** The maps between total spaces of families given by a map between the bases of the families and maps between the corresponding members of the families. *)


Definition bandfmap (X Y:UU)(f: X -> Y) (P:X -> UU)(Q: Y -> UU)(fm: forall x:X, P x -> (Q (f x))): total2 X P -> total2 Y Q:= fun xp:_ =>
match xp with
tpair x p => tpair Y Q (f x) (fm x p)
end.

Theorem isweqbandfmap  (X Y:UU)(f: X -> Y) (P:X -> UU)(Q: Y -> UU)(fm: forall x:X, P x -> (Q (f x)))(isf: isweq _ _ f)(isfm: forall x:X, isweq _ _ (fm x)): isweq _ _ (bandfmap _ _ _ P Q fm).
Proof. intros. set (f1:= totalfun _ P _ fm). set (is1:= isweqfibtototal X P (fun x:X => Q (f x)) fm isfm).  set (f2:= fpmap _ _ f Q).  set (is2:= isweqfpmap _ _ f Q isf). 
assert (h: forall xp: total2 X P, paths _ (f2 (f1 xp)) (bandfmap _ _ f P Q fm xp)). intro. destruct xp. apply idpath.  apply (isweqhomot _ _ _ _ h (twooutof3c _ _ _ f1 f2 is1 is2)). Defined.





(** ** Homotopy fiber products. *)


Definition hfp {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= total2 X (fun x:X => hfiber _ _ f' (f x)).
Definition hfppair {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= tpair X (fun x:X => hfiber _ _ f' (f x)).
Definition hfppr1 {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= pr21 X (fun x:X => hfiber _ _ f' (f x)).






(** * Direct products, pairwise coproducts and weak equivalences. *)



(** ** Weak equivalences and pairwise direct products. *)



 
Corollary isweqdirprodf (X Y X' Y':UU)(f:X-> Y)(f':X' -> Y')(is:isweq _ _ f)(is': isweq _ _ f'): isweq _ _ (dirprodf _ _ _ _ f f').
Proof. intros.  apply (isweqbandfmap X Y f (fun x:X => X') (fun y:Y => Y') (fun x:X => f') is (fun x:X => is')). Defined. 


Definition weqdirprodf (X Y X' Y':UU)(w: weq X Y)(w': weq X' Y') : weq (dirprod X X') (dirprod Y Y').
Proof. intros. destruct w. destruct w'. split with (dirprodf _ _ _ _ t t0).  apply isweqdirprodf. apply x.  apply x0.  Defined. 


Definition weqtodirprodwithunit (X:UU): weq X (dirprod X unit).
Proof. intros. set (f:=fun x:X => dirprodpair X unit x tt). split with f.  set (g:= fun xu:dirprod X unit => pr21 _ _ xu). 
assert (egf: forall x:X, paths _ (g (f x)) x). intro. apply idpath.
assert (efg: forall xu:_, paths _ (f (g xu)) xu). intro. destruct xu. destruct x. apply idpath.    
apply (gradth _ _ f g egf efg). Defined.


(** ** Basics on pairwise coproducts (disjoint unions).  *)



Inductive coprod (X Y:UU) :UU := ii1: X -> coprod X Y | ii2: Y -> coprod X Y.



Definition sumofmaps {X Y Z:UU}(fx: X -> Z)(fy: Y -> Z): (coprod X Y) -> Z := fun xy:_ => match xy with ii1 x => fx x | ii2 y => fy y end.


Definition boolascoprod: weq (coprod unit unit) bool.
Proof. set (f:= fun xx: coprod unit unit => match xx with ii1 t => true | ii2 t => false end). split with f. 
set (g:= fun t:bool => match t with true => ii1 _ _ tt | false => ii2 _ _ tt end). 
assert (egf: forall xx:_, paths _ (g (f xx)) xx). destruct xx. destruct u. apply idpath. destruct u. apply idpath. 
assert (efg: forall t:_, paths _ (f (g t)) t). destruct t. apply idpath. apply idpath. 
apply (gradth _ _ f g egf efg). Defined.  


Definition coprodasstor (X Y Z:UU): coprod (coprod X Y) Z -> coprod X (coprod Y Z).
Proof. intros. destruct X0.  destruct c.  apply (ii1 _ _ x). apply (ii2 _ _ (ii1 _ _ y)). apply (ii2 _ _ (ii2 _ _ z)). Defined.

Definition coprodasstol (X Y Z: UU): coprod X (coprod Y Z) -> coprod (coprod X Y) Z.
Proof. intros. destruct X0.  apply (ii1 _ _ (ii1 _ _ x)). destruct c.   apply (ii1 _ _ (ii2 _ _ y)). apply (ii2 _ _ z). Defined.

Theorem isweqcoprodasstor (X Y Z:UU): isweq _ _ (coprodasstor X Y Z).
Proof. intros. set (f:= coprodasstor X Y Z). set (g:= coprodasstol X Y Z).
assert (egf: forall xyz:_, paths _ (g (f xyz)) xyz). intro. destruct xyz.  destruct c. apply idpath. apply idpath. apply idpath. 
assert (efg: forall xyz:_, paths _ (f (g xyz)) xyz). intro.  destruct xyz.  apply idpath.  destruct c. apply idpath. apply idpath.
apply (gradth _ _ f g egf efg). Defined. 

Corollary isweqcoprodasstol (X Y Z:UU): isweq _ _ (coprodasstol X Y Z).
Proof. intros. apply (isweqinvmap _ _ _ (isweqcoprodasstor X Y Z)). Defined.

Definition weqcoprodasstor (X Y Z:UU):= weqpair _ _ _ (isweqcoprodasstor X Y Z).

Definition weqcoprodasstol (X Y Z:UU):= weqpair _ _ _ (isweqcoprodasstol X Y Z).

Definition coprodcomm (X Y:UU): coprod X Y -> coprod Y X := fun xy:_ => match xy with ii1 x => ii2 _ _ x | ii2 y => ii1 _ _ y end. 

Theorem isweqcoprodcomm (X Y:UU): isweq _ _ (coprodcomm X Y).
Proof. intros. set (f:= coprodcomm X Y). set (g:= coprodcomm Y X).
assert (egf: forall xy:_, paths _ (g (f xy)) xy). intro. destruct xy. apply idpath. apply idpath.
assert (efg: forall yx:_, paths _ (f (g yx)) yx). intro. destruct yx. apply idpath. apply idpath.
apply (gradth _ _ f g egf efg). Defined. 

Definition weqcoprodcomm (X Y:UU):= weqpair _ _ _ (isweqcoprodcomm X Y).

Theorem isweqcoprodwithempty (X Y:UU)(nf:Y -> empty): isweq _ _ (ii1 X Y).
Proof. intros. set (f:= ii1 X Y). set (g:= fun xy:coprod X Y => match xy with ii1 x => x | ii2 y => initmap _ (nf y) end).  
assert (egf: forall x:X, paths _ (g (f x)) x). intro. apply idpath. 
assert (efg: forall xy: coprod X Y, paths _ (f (g xy)) xy). intro. destruct xy. apply idpath. apply (initmap _ (nf y)).  
apply (gradth _ _ f g egf efg). Defined.  



Theorem isweqfromcoprodwithempty (X:UU): isweq _ _ (fun ex: coprod empty X => match ex with ii1 e => initmap _ e | ii2 x => x end).
Proof. intros. set (f:=fun ex: coprod empty X => match ex with ii1 e => initmap _ e | ii2 x => x end). set (g:= ii2 empty X).
assert (egf: forall ex:_, paths _ (g (f ex)) ex). intro. destruct ex.  destruct e. apply idpath.
assert (efg: forall x:_, paths _ (f (g x)) x). intro. apply idpath. 
apply (gradth _ _ f g egf efg). Defined.

Definition weqfromcoprodwithempty (X:UU):= weqpair _ _ _ (isweqfromcoprodwithempty X). 


Definition coprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y'): coprod X Y -> coprod X' Y' := fun xy: coprod X Y =>
match xy with
ii1 x => ii1 _ _ (f x)|
ii2 y => ii2 _ _ (g y)
end. 


Theorem isweqcoprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y')(isf:isweq _ _ f)(isg: isweq _ _ g): isweq _ _ (coprodf _ _ _ _ f g).
Proof. intros. set (finv:= invmap _ _ f isf). set (ginv:= invmap _ _ g isg). set (ff:=coprodf _ _ _ _ f g). set (gg:=coprodf _ _ _ _ finv ginv). 
assert (egf: forall xy: coprod X Y, paths _ (gg (ff xy)) xy). intro. destruct xy. simpl. apply (maponpaths _ _ (ii1 X Y) _ _ (weqgf _ _ _ isf x)).     apply (maponpaths _ _ (ii2 X Y) _ _ (weqgf _ _ _ isg y)).
assert (efg: forall xy': coprod X' Y', paths _ (ff (gg xy')) xy'). intro. destruct xy'. simpl.  apply (maponpaths _ _ (ii1 X' Y') _ _ (weqfg _ _ _ isf x)).     apply (maponpaths _ _ (ii2 X' Y') _ _ (weqfg _ _ _ isg y)). 
apply (gradth _ _ ff gg egf efg). Defined. 



Definition weqcoprodf (X Y X' Y' :UU)(w1: weq X Y)(w2: weq X' Y'): weq (coprod X X') (coprod Y Y').
Proof. intros. destruct w1. destruct w2. split with (coprodf _ _ _ _ t t0). apply (isweqcoprodf _ _ _ _ _ _ x x0).  Defined.




Lemma negpathsii1ii2 (X Y:UU)(x:X)(y:Y): neg (paths _ (ii1 _ _ x) (ii2 _ _ y)).
Proof. intros. unfold neg. intro. set (dist:= fun xy: coprod X Y => match xy with ii1 x => unit | ii2 y => empty end). apply (transportf _ dist _ _ X0 tt). Defined.

Lemma negpathsii2ii1  (X Y:UU)(x:X)(y:Y): neg (paths _ (ii2 _ _ y) (ii1 _ _ x)).
Proof. intros. unfold neg. intro. set (dist:= fun xy: coprod X Y => match xy with ii1 x => empty | ii2 y => unit end). apply (transportf _ dist _ _ X0 tt). Defined.










(** ** Coproducts and direct products. *)


Definition rdistrtocoprod (X Y Z:UU): dirprod X (coprod Y Z) -> coprod (dirprod X Y) (dirprod X Z).
Proof. intros. destruct X0.  destruct x.   apply (ii1 _ _ (dirprodpair _ _ t y)). apply (ii2 _ _ (dirprodpair _ _ t z)). Defined.


Definition rdistrtoprod (X Y Z:UU): coprod (dirprod X Y) (dirprod X Z) ->  dirprod X (coprod Y Z).
Proof. intros. destruct X0.  destruct d. apply (dirprodpair _ _ t (ii1 _ _ x)). destruct d. apply (dirprodpair _ _ t (ii2 _ _ x)). Defined. 


Theorem isweqrdistrtoprod (X Y Z:UU): isweq _ _ (rdistrtoprod X Y Z).
Proof. intros. set (f:= rdistrtoprod X Y Z). set (g:= rdistrtocoprod X Y Z). 
assert (egf: forall a:_, paths _ (g (f a)) a).  intro. destruct a. destruct d. apply idpath. destruct d. apply idpath. 
assert (efg: forall a:_, paths _ (f (g a)) a). intro. destruct a. destruct x.  apply idpath. apply idpath.
apply (gradth _ _ f g egf efg). Defined.


Corollary isweqrdistrtocoprod (X Y Z:UU): isweq _ _ (rdistrtocoprod X Y Z).
Proof. intros. apply (isweqinvmap _ _ _ (isweqrdistrtoprod X Y Z)). Defined.

Definition weqrdistrtoprod (X Y Z: UU):= weqpair _ _ _ (isweqrdistrtoprod X Y Z).

Definition weqrdistrtocoprod (X Y Z: UU):= weqpair _ _ _ (isweqrdistrtocoprod X Y Z).
 




(** * Extentionality axioms. *)

(** Summary: We consider two axioms which address functional extensionality. The first one is etacorrection  which compensates for the absense of eta-reduction in Coq8.3 Eta-reduction is expected to be included as a  basic property of the language in Coq8.4 which will make this axiom and related lemmas unnecessary. The second axiom funcontr is the functional extensionality for dependent functions formulated as the condition that the space of section of a family with contractible fibers is contractible. We will show in .... that it follows from the univalence axiom applied on a higher universe level. *)


(** ** Axioms and their basic corollaries. *)

(** etacorrection *)

Axiom etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths _ f (fun t:T => f t). 

Lemma isweqetacorrection (T:UU)(P:T -> UU): isweq _ _ (fun f: forall t:T, P t => (fun t:T => f t)).
Proof. intros.  apply (isweqhomot _ _ (fun f: forall t:T, P t => f) (fun f: forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => etacorrection _ P f) (idisweq _)). Defined. 

Lemma etacorrectiononpaths (T:UU)(P:T->UU)(s1:forall t:T, P t)(s2:forall t:T, P t): paths _ (fun t:T => s1 t) (fun t:T => s2 t)-> paths _ s1 s2. 
Proof. intros. set (ec:= fun s:forall t:T, P t => (fun t:T => s t)). set (is:=isweqetacorrection T P). apply (pathsweq2 _ _ ec is s1 s2 X). Defined. 

Definition etacor (X:UU)(Y:UU)(f:X -> Y):paths _ f (fun x:X => f x) := etacorrection X (fun T:X => Y) f.

Lemma etacoronpaths (X:UU)(Y:UU)(f1:X->Y)(f2:X->Y):paths _ (fun x:X => f1 x) (fun x:X => f2 x) -> paths _ f1 f2. 
Proof. intros. set (ec:= fun f:X->Y => (fun x:X => f x)). set (is:=isweqetacorrection X (fun x:X => Y)). apply (pathsweq2 _ _ ec is f1 f2 X0). Defined.


(** * Preambule. *)

(* Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Definition UU:=Type. (* This fixes a type universe which we will be working with. *)


(* We are using the standard library definitions for unit (one point set), Empty_set and nat (the set of natural numbers). *)

Definition empty:=Empty_set.

Definition initmap (X:UU) : empty -> X.
Proof. intros.  destruct H. Defined. 



(** * Some standard constructions not using equality. *)

(**  ** Dependent sums (fibrations) *)


Inductive total2 (T:UU) (P:T -> UU) : UU := tpair: forall t:T, forall x: P t, total2 T P.


Definition pr21 (T:UU) (P:T -> UU) (z: total2 T P) : T := 
match z with 
tpair t x => t
end.  


Definition pr22 (T:UU) (P:T -> UU) (z: total2 T P) : P (pr21 _ _ z):=
match z with
tpair t x => x
end. 



(** ** Pairwise direct products. *)




Definition dirprod (X:UU)(Y:UU):= total2 X (fun x:X => Y).
Definition dirprodpair (X:UU)(Y:UU):= tpair X (fun x:X => Y).

Definition dirprodadj (X Y Z:UU): ((dirprod X Y) -> Z) -> (X -> Y -> Z) := fun f:_ => fun x:X => fun y:Y => f (dirprodpair _ _ x y).



(** A retract lemma *)


Lemma adjevretract (X Y:UU): forall f: X-> Y, paths _ (adjev2 _ _ (adjev (X -> Y) Y f)) f.
Proof. intros. unfold adjev2. unfold adjev. apply (pathsinv0 _ _ _ (etacorrection _ _ f)). Defined. 


*)

(** funcontr *)



Axiom  funcontr: forall X:UU, forall P: X -> UU,  (forall x:X, iscontr (P x)) ->  iscontr (forall x:X, P x).

Corollary funcontrtwice (X:UU)(P: X-> X -> UU)(is: forall (x x':X), iscontr (P x x')): iscontr (forall (x x':X), P x x').
Proof. intros. 
assert (is1: forall x:X, iscontr (forall x':X, P x x')). intros. apply (funcontr _ _ (is x)). apply (funcontr _ _ is1). Defined. 


(** Proof of the fact that the funextmap from [paths _ s1 s2] to [forall t:T, paths _ (s1 t) (s2 t)] is a weak equivalence - a strong form 
of functional extensionality for sections of general families. *)


Definition funextmap (T:UU) (P:T -> UU) (f:forall t:T, P t)( g: forall t:T, P t): (paths (forall t:T, P t) f g) -> (forall t:T, paths (P t) (f t) (g t)).
Proof. intros. induction X. apply idpath. Defined. 


Lemma funextweql1 (T:UU)(P:T -> UU)(g: forall t:T, P t): iscontr (total2 _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t))).
Proof. intros. set (X:= forall t:T, coconustot (P t) (g t)). assert (is1: iscontr X). apply (funcontr  _ (fun t:T => coconustot (P t) (g t)) (fun t:T => iscontrcoconustot (P t) (g t))).  set (Y:= total2 _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t))). set (p:= fun z: X => tpair _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t)) (fun t:T => pr21 _ _ (z t)) (fun t:T => pr22 _ _ (z t))).  set (s:= fun u:Y => (fun t:T => coconustotpair (P t) (g t) ((pr21 _ _ u) t) ((pr22 _ _ u) t))).  set (etap:= fun u: Y => tpair _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t)) (fun t:T => ((pr21 _ _ u) t)) (pr22 _ _ u)).

assert (eps: forall u:Y, paths _ (p (s u)) (etap u)).  intro.  destruct u. unfold p. unfold s. unfold etap.   simpl. assert (ex: paths _ x (fun t0:T => x t0)). apply etacorrection.  induction ex. apply idpath. 

assert (eetap: forall u:Y, paths _ (etap u) u). intro. unfold etap. destruct u. simpl.


set (ff:= fun fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))) => tpair _ (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0)) (fun t0:T => (pr21 _ _ fe) t0) (pr22 _ _ fe)). 

assert (isweqff: isweq _ _ ff). apply (isweqfpmap (forall t:T, P t) (forall t:T, P t) (fun f:forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => forall t:T, paths (P t) (f t) (g t)) (isweqetacorrection T P)). 

assert (ee: forall fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))), paths _ (ff (ff fe)) (ff fe)). intro. apply idpath.  assert (eee: forall fe: (total2 (forall t0 : T, P t0) (fun f : forall t0 : T, P t0 => forall t0 : T, paths (P t0) (f t0) (g t0))), paths _ (ff  fe) fe). intro. apply (pathsweq2 _ _ ff isweqff _ _ (ee fe)).  

apply (eee (tpair _ _ t x)). assert (eps0: forall u: Y, paths _ (p (s u)) u). intro. apply (pathscomp0 _ _ _ _ (eps u) (eetap u)). 
 
apply (contrl1' X Y p s eps0). assumption. Defined. 





Theorem isweqfunextmap(T:UU)(P:T -> UU)(f: forall t:T, P t) (g: forall t:T, P t): isweq _ _ (funextmap T P f g). 
Proof. intros. set (tmap:= fun ff: total2 _ (fun f0: forall t:T, P t, paths _ f0 g) => tpair _ (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)) (pr21 _ _ ff) (funextmap _ P (pr21 _ _ ff) g (pr22 _ _ ff))). assert (is1: iscontr (total2 _ (fun f0: forall t:T, P t, paths _ f0 g))). apply (iscontrcoconustot _ g).   assert (is2:iscontr (total2 _ (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)))). apply funextweql1.  
assert (isweq _ _ tmap).  apply (ifcontrcontrthenweq _ _ tmap is1 is2).  apply (isweqtotaltofib _ (fun f0: forall t:T, P t, paths _ f0 g) (fun f0:forall t:T, P t => forall t:T, paths _ (f0 t) (g t)) (fun f0:forall t:T, P t =>  (funextmap _ P f0 g)) X f).  Defined. 


Definition funextsec (T:UU) (P: T-> UU) (s1: forall t:T, P t)(s2: forall t:T, P t): (forall t:T, paths _ (s1 t) (s2 t)) -> paths _ s1 s2 := invmap _ _ (funextmap _ _ s1 s2) (isweqfunextmap _ _ s1 s2).


Theorem isweqfunextsec(T:UU)(P:T -> UU)(f: forall t:T, P t) (g: forall t:T, P t): isweq _ _ (funextsec T P f g).
Proof. intros. apply (isweqinvmap _ _ (funextmap _ _ f g) (isweqfunextmap _ _ f g)). Defined. 


Theorem weqfunextsec (T:UU)(P:T -> UU)(f: forall t:T, P t) (g: forall t:T, P t): weq  (paths _ f g) (forall t:T, paths _ (f t) (g t)).
Proof. intros. split with (funextmap T P f g). apply isweqfunextmap. Defined. 


(** The following definitions introduce the particular cases the preceeding results in the case of functions i.e. section of constsnant families. *)


Definition funextmapfun (X:UU)(Y:UU)(f:X->Y)(g:X->Y): (paths _ f g) -> (forall x:X, paths _ (f x) (g x)) := funextmap X (fun x:X => Y) f g.  

Definition  isweqfunextmapfun (X:UU)(Y:UU)(f:X->Y)(g:X->Y): isweq _ _ (funextmapfun _ _ f g) := isweqfunextmap X (fun x:X => Y) f g.

Definition funextsecfun (X:UU)(Y:UU)(f:X->Y)(g:X->Y):  (forall x:X, paths _ (f x) (g x)) -> (paths _ f g) := funextsec X (fun x:X => Y) f g. 






(** ** Sections of "double fibration" [(P: T -> UU)(PP: forall t:T, P t -> UU)] and pairs of sections. *)

Definition totaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) -> forall x:X, total2 (P x) (PP x).
Proof. intros. induction X0. split with (t x). apply (x0 x). Defined.


Definition foralltototal  (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU):  (forall x:X, total2 (P x) (PP x)) -> total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)).
Proof. intros. split with (fun x:X => pr21 _ _ (X0 x)). apply (fun x:X => pr22 _ _ (X0 x)). Defined.

Lemma lemmaeta1 (X:UU)(P:X->UU)(Q:(forall x:X, P x) -> UU)(s0: forall x:X, P x)(q: Q (fun x:X => (s0 x))): paths (total2 _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x)))) (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) s0 q) (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) (fun x:X => (s0 x)) q). 
Proof. intros. set (ff:= fun tp:total2 _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) => tpair _ _ (fun x:X => pr21 _ _ tp x) (pr22 _ _ tp)). assert (isweq _ _ ff).  apply (isweqfpmap _ _ (fun s: forall x:X, P x => (fun x:X => (s x))) Q (isweqetacorrection X P)). assert (ee: paths _ (ff (tpair (forall x : X, P x)
        (fun s : forall x : X, P x => Q (fun x : X => s x)) s0 q)) (ff (tpair (forall x : X, P x)
        (fun s : forall x : X, P x => Q (fun x : X => s x))
        (fun x : X => s0 x) q))). apply idpath. 

apply (pathsweq2 _ _ ff X0 _ _ ee). Defined. 



Definition totaltoforalltototal(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss:total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) ): paths _ (foralltototal _ _ _ (totaltoforall _ _ _ ss)) ss.
Proof. intros.  induction ss. unfold foralltototal. unfold totaltoforall.  simpl. 
set (et:= fun x:X => t x). 

assert (paths _ (tpair (forall x0 : X, P x0) (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) t x) 
(tpair (forall x0 : X, P x0) (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x)). apply (lemmaeta1 X P (fun s: forall x:X, P x =>  forall x:X, PP x (s x)) t x).  

assert (ee: paths 
     (total2 (forall x0 : X, P x0)
        (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)))
     (tpair (forall x0 : X, P x0)
        (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et
        x)
     (tpair (forall x0 : X, P x0)
        (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et (fun x0 : X => x x0))). assert (eee: paths _ x (fun x0:X => x x0)). apply etacorrection. induction eee. apply idpath. induction ee. apply pathsinv0. assumption. Defined. 



Definition foralltototaltoforall(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss: forall x:X, total2 (P x) (PP x)): paths _ (totaltoforall _ _ _ (foralltototal _ _ _ ss)) ss.
Proof. intros. unfold foralltototal. unfold totaltoforall.  simpl. assert (ee: forall x:X, paths _ (tpair (P x) (PP x) (pr21 (P x) (PP x) (ss x)) (pr22 (P x) (PP x) (ss x))) (ss x)).  intro. apply (pathsinv0 _ _ _ (tppr (P x) (PP x) (ss x))).  apply (funextsec). assumption. Defined.

Theorem isweqforalltototal (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (foralltototal X P PP).
Proof. intros.  apply (gradth _ _ (foralltototal X P PP) (totaltoforall X P PP) (foralltototaltoforall  X P PP) (totaltoforalltototal X P PP)). Defined. 

Theorem isweqtotaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (totaltoforall X P PP).
Proof. intros.  apply (gradth _ _  (totaltoforall X P PP) (foralltototal X P PP)  (totaltoforalltototal X P PP) (foralltototaltoforall  X P PP)). Defined. 




(** ** Homotopy fibers of the map [forall x:X, P x -> forall x:X, Q x]. *) 



Definition maponsec (X:UU)(P:X -> UU)(Q:X-> UU)(f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) := 
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).



Definition hfibertoforall (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): hfiber _ _ (maponsec _ _ _ f) s -> forall x:X, hfiber _ _ (f x) (s x).
Proof. intro. intro. intro. intro. intro.  unfold hfiber. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).  

set (themap := fun a:_ => map2 (map1 a)). assumption. Defined. 



Definition foralltohfiber  (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): (forall x:X, hfiber _ _ (f x) (s x)) -> hfiber _ _ (maponsec _ _ _ f) s.
Proof.  intro. intro. intro. intro.   intro. unfold hfiber. 

set (map2inv := foralltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).
set (map1inv :=  totalfun (forall x : X, P x)  (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s)).
set (themap := fun a:_=> map1inv (map2inv a)). assumption. Defined. 


Theorem isweqhfibertoforall  (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (hfibertoforall _ _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).  

assert (is1: isweq _ _ map1). apply (isweqfibtototal _ _ _ (fun pointover: forall x:X, P x => funextmap _ _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => (isweqfunextmap _ _ (fun x : X => f x (pointover x)) s))).

assert (is2: isweq _ _ map2). apply isweqtotaltoforall.

apply (twooutof3c _ _ _ map1 map2 is1 is2). Defined.


Theorem isweqforalltohfiber  (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (foralltohfiber _ _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map2inv := foralltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).

assert (is2: isweq _ _ map2inv). apply (isweqforalltototal X P (fun x:X => (fun pointover : P x => paths (Q x) (f x pointover) (s x)))).

set (map1inv :=  totalfun (forall x : X, P x)  (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (forall x : X, Q x) (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s)).

assert (is1: isweq _ _ map1inv). apply (isweqfibtototal _ _ _ (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => (isweqfunextsec _ _ (fun x : X => f x (pointover x)) s))).

apply (twooutof3c _ _ _ map2inv map1inv is2 is1). Defined. 






(** The map between section spaces (dependent products) defined by a family of maps P x -> Q x is a weak equivalence if all maps P x -> Q x are weak equivalences. *)




Corollary isweqmaponsec (X:UU)(P:X-> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(isx: forall x:X, isweq _ _ (f x)): isweq _ _ (maponsec _ _ _ f). 
Proof. intros. unfold isweq.  intro.
assert (is1: iscontr (forall x:X, hfiber _ _ (f x) (y x))). assert (is2: forall x:X, iscontr (hfiber _ _ (f x) (y x))). unfold isweq in isx. intro. apply (isx x (y x)). apply funcontr. assumption. 
apply (iscontrxifiscontry _ _ (hfibertoforall _ P Q f y) (isweqhfibertoforall _ P Q f y) is1). Defined. 





(** ** The map between section spaces (dependent products) defined by f: Y -> X. *)




Definition maponsec1l0 (X:UU)(P:X -> UU)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x): (forall x:X, P x) := (fun x:X => transportf X P _ _ (h x) (s (f x))).

Lemma maponsec1l1  (X:UU)(P:X -> UU)(x:X)(s:forall x:X, P x): paths _ (maponsec1l0 _ P (fun x:X => x) (fun x:X => idpath _ x) s x) (s x). 
Proof. intros. unfold maponsec1l0.   apply idpath. Defined. 


Lemma maponsec1l2 (X:UU)(P:X -> UU)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x)(x:X): paths _ (maponsec1l0 _ P f h s x) (s x).
Proof. intro. intro. intro. intro. intros.  

set (map:= fun ff: total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x) => maponsec1l0 X P (pr21 _ _ ff) (pr22 _ _ ff) s x).
assert (is1: iscontr (total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x))). apply funextweql1. assert (e: paths _ (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) f h) (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) (fun x0:X => x0) (fun x0:X => idpath _ x0))). apply contrl2.  assumption.  apply (maponpaths _ _ map _ _ e). Defined. 


Theorem isweqmaponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y)(is:isweq _ _ f):isweq _ _ (maponsec1 _ _ P f).
Proof. intros.
 
set (map:= maponsec1 _ _ P f).
set (invf:= invmap _ _ f is). set (e1:= weqfg _ _ f is). set (e2:= weqgf _ _ f is).
set (im1:= fun sx: forall x:X, P (f x) => (fun y:Y => sx (invf y))).
set (im2:= fun sy': forall y:Y, P (f (invf y)) => (fun y:Y => transportf _ _ _ _ (weqfg _ _ _ is y) (sy' y))).
set (invmapp := (fun sx: forall x:X, P (f x) => im2 (im1 sx))). 

assert (efg0: forall sx: (forall x:X, P (f x)), forall x:X, paths _ ((map (invmapp sx)) x) (sx x)).  intro. intro. unfold map. unfold invmapp. unfold im1. unfold im2. unfold maponsec1.  simpl. fold invf.  set (ee:=e2 x).  fold invf in ee.

set (e3x:= fun x0:X => pathsweq2 _ _ f is (invf (f x0)) x0 (weqfg X Y f is (f x0))). set (e3:=e3x x). assert (e4: paths _ (weqfg X Y f is (f x)) (maponpaths _ _ f _ _ e3)). apply (pathsinv0 _ _ _ (pathsweq4 _ _ f is (invf (f x)) x _)).

assert  (e5:paths _ (transportf Y P (f (invf (f x))) (f x) (weqfg X Y f is (f x)) (sx (invf (f x)))) (transportf Y P (f (invf (f x))) (f x) (maponpaths _ _ f _ _ e3) (sx (invf (f x))))). apply (maponpaths _ _ (fun e40:_ => (transportf Y P (f (invf (f x))) (f x) e40 (sx (invf (f x))))) _ _ e4).

assert (e6: paths _ (transportf Y P (f (invf (f x))) (f x) (maponpaths X Y f (invf (f x)) x e3) (sx (invf (f x)))) (transportf X (fun x:X => P (f x)) _ _ e3 (sx (invf (f x))))). apply (pathsinv0 _ _ _ (functtransportf _ _ f P _ _ e3 (sx (invf (f x))))).

set (ff:= fun x:X => invf (f x)).
assert (e7: paths _ (transportf X (fun x : X => P (f x)) (invf (f x)) x e3 (sx (invf (f x)))) (sx x)). apply (maponsec1l2 _ (fun x:X => P (f x))ff e3x sx x).  apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e5 e6) e7).

assert (efg: forall sx: (forall x:X, P (f x)), paths _  (map (invmapp sx)) sx). intro. apply (funextsec _ _ _ _ (efg0 sx)).

assert (egf0: forall sy: (forall y:Y, P y), forall y:Y, paths _ ((invmapp (map sy)) y) (sy y)). intros. unfold invmapp. unfold map.  unfold im1. unfold im2. unfold maponsec1. 

set (ff:= fun y:Y => f (invf y)). fold invf. apply (maponsec1l2 Y P ff (weqfg X Y f is) sy y). 
assert (egf: forall sy: (forall y:Y, P y), paths _  (invmapp (map sy)) sy). intro. apply (funextsec _ _ _ _ (egf0 sy)). 

apply (gradth _ _ map invmapp egf efg). Defined. 
































(** * Basics about h-levels. *)



(** ** h-levels of types. *)


Fixpoint isofhlevel (n:nat) (X:UU): UU:=
match n with
O => iscontr X |
S m => forall x:X, forall x':X, (isofhlevel m (paths _ x x'))
end.



Theorem hlevelretract (n:nat)(X:UU)(Y:UU)(p:X -> Y)(s:Y ->X)(eps: forall y:Y, paths _  (p (s y)) y): (isofhlevel n X) -> (isofhlevel n Y).
Proof. intro. induction n. intros. apply (contrl1' _ _ p s eps X0). 
intros. unfold isofhlevel. intros. unfold isofhlevel in X0. assert (is: isofhlevel n (paths _ (s x) (s x'))).  apply X0. set (s':= maponpaths _ _ s x x'). set (p':= pathssec2 _ _ s p eps x x'). set (eps':= pathssec3 _ _ s p eps x x').  apply (IHn _ _ p' s' eps' is). Defined. 

Corollary  isofhlevelweqf (n:nat)(X:UU)(Y:UU)(f:X -> Y)(is: isweq _ _ f): (isofhlevel n X) -> (isofhlevel n Y).
Proof. intros.  apply (hlevelretract n _ _ f (invmap _ _ f is) (weqfg _ _ f is)). assumption. Defined. 

Corollary  isofhlevelweqb (n:nat)(X:UU)(Y:UU)(f:X -> Y)(is: isweq _ _ f): (isofhlevel n Y) -> (isofhlevel n X).
Proof. intros.  apply (hlevelretract n _ _ (invmap _ _ f is) f (weqgf _ _ f is)). assumption. Defined. 

Lemma isofhlevelsn (n:nat)(X:UU) : (X -> isofhlevel (S n) X) -> isofhlevel (S n) X.
Proof. intros.  simpl.  intros.  apply (X0 x x x'). Defined.


Lemma isofhlevelssn (n:nat)(X:UU): (forall x:X, isofhlevel (S n) (paths _ x x)) -> isofhlevel (S (S n)) X.
Proof. intros. simpl.  intro. intro.  change (forall (x0 x'0 : paths X x x'), isofhlevel n (paths (paths X x x') x0 x'0) ) with (isofhlevel (S n) (paths _ x x')). assert (paths _ x x' -> (isofhlevel (S n) (paths _ x x'))). intro. destruct X1. apply (X0 x). apply  (isofhlevelsn n _ X1). Defined. 


Theorem isapropunit: isofhlevel (S O) unit.
Proof. intros. unfold isofhlevel. intros. 
assert (c:paths unit x x'). induction x. induction x'. eapply idpath.
assert (forall g:paths unit x x', paths _ g c). intros. assert (e:paths (paths unit x x') c c).   apply idpath. induction c. induction x. apply unitl3. apply (iscontrpair _ c X). Defined.  



Theorem isapropifcontr (X:UU): (iscontr X) -> (isofhlevel (S O) X).
Proof. intros. set (f:= fun x:X => tt). assert (is: isweq _ _ f). apply isweqcontrtounit.  assumption. apply (isofhlevelweqb (S O) X unit f is).  apply isapropunit. Defined. 


Theorem hlevelsincl (n:nat) (T:UU) : isofhlevel n T -> isofhlevel (S n) T.
Proof. intro.   induction n. intro. apply (isapropifcontr T). intro.  intro. change (forall t1 t2:T, isofhlevel (S n) (paths _ t1 t2)). intros. change (forall t1 t2 : T, isofhlevel n (paths _ t1 t2)) in X. set (XX := X t1 t2). apply (IHn _ XX).  Defined.


Corollary isofhlevelcontr (n:nat)(X:UU): iscontr X -> isofhlevel n X.
Proof. intro. induction n. intros. assumption. 
intros. simpl. intros. assert (is: iscontr (paths _ x x')). apply (isapropifcontr _ X0 x x'). apply (IHn _ is). Defined.

Lemma iscontraprop1 (X:UU): (isofhlevel (S O) X) -> (X -> (iscontr X)).
Proof. intros. unfold iscontr. split with X1. intro.  unfold isofhlevel in X0.  set (is:= X0 t X1). apply (pr21 _ _ is). 
Defined. 

Lemma iscontraprop1inv (X:UU): (X -> iscontr X) -> (isofhlevel (S O) X).
Proof. intros. assert (X -> isofhlevel (S O) X). intro.  apply (hlevelsincl O _ (X0 X1)). apply (isofhlevelsn O _ X1). Defined.






(** ** h-levels of functions *)


Definition isofhlevelf (n:nat)(X:UU)(Y:UU)(f:X -> Y): UU := forall y:Y, isofhlevel n (hfiber _ _ f y).


Lemma isofhlevelfweq (n:nat)(X Y:UU)(f:X -> Y): isweq _ _ f -> isofhlevelf n _ _ f.
Proof. intros.  unfold isofhlevelf. intro.  apply (isofhlevelcontr n). apply (X0 y). Defined.

Theorem isofhlevelfpmap (n:nat)(X Y:UU)(f:X -> Y)(Q:Y -> UU): isofhlevelf n _ _ f -> isofhlevelf n _ _ (fpmap _ _ f Q).
Proof. intros. unfold isofhlevelf. unfold isofhlevelf in X0.  intro. set (yy:= pr21 _ _ y). set (g:= hfiberfpmap _ _ f Q y). set (is:= isweqhfiberfp _ _ f Q y). set (isy:= X0 yy).  apply (isofhlevelweqb n _ _ _ is isy). Defined. 



Theorem isofhlevelfpr21 (n:nat)(X:UU)(P:X -> UU)(is: forall x:X, isofhlevel n (P x)):isofhlevelf n _ _ (pr21 X P).
Proof. intros. unfold isofhlevelf. intro. rename y into x. apply (isofhlevelweqf n _ _ (fibmap1 _ _ x) (isweqfibmap1 _ _ x)  (is x)). Defined.


Theorem isofhlevelfhomot (n:nat)(X Y:UU)(f f':X -> Y)(h: forall x:X, paths _ (f x) (f' x)): isofhlevelf n _ _ f -> isofhlevelf n _ _ f'.
Proof. intros. unfold isofhlevelf. intro. 
set (ff:= (fun z:(hfiber _ _ f' y) =>
match z with 
(tpair x e) => hfiberpair _ _ f y x (pathscomp0 _ _ _ _ (h x) e)
end)). 

set (gg:= (fun z:(hfiber _ _ f y) =>
match z with
(tpair x e) => hfiberpair _ _ f' y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) e)
end)). 

assert (egf: forall z:(hfiber _ _ f' y), paths _ (gg (ff z)) z). intros. destruct z.  rename x into e. rename t into x.
apply (constr3 _ _ f' y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ (h x) e)) e (pathsinv1l _ (f x) (f' x) y (h x) e)).
apply (hlevelretract n _ _ gg ff egf (X0 y)). Defined.



Theorem isofhlevelfinfibseq (n:nat)(X Y:UU)(f:X-> Y): isofhlevel n X -> isofhlevel (S n) Y -> isofhlevelf n _ _ f.
Proof. intro. induction n.  intros.
assert (is1: isofhlevel O Y). apply (iscontraprop1 Y X1 (f (pr21 _ _ X0))). apply (ifcontrcontrthenweq _ _ f X0 is1).

intros.  unfold isofhlevelf. simpl.  
assert  (is1: forall x' x:X, isofhlevel n (paths _ x' x)). simpl in X0.  assumption.  
assert (is2: forall y' y:Y, isofhlevel (S n) (paths _ y' y)). simpl in X1.  simpl. assumption.
assert (is3: forall (y:Y)(x:X)(xe': hfiber _ _ f y), isofhlevelf n _ _ (d3f _ _ f y x xe')).  intros. apply (IHn _ _ (d3f _ _ f y x xe') (is1 (pr21 _ _ xe') x) (is2 (f x) y)). 
assert (is4: forall (y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y), isofhlevel n (paths _ (hfiberpair _ _ f y x e) xe')). intros.
apply (isofhlevelweqb n _ _ _ (isfibseq4 _ _ f y x xe' e) (is3 y x xe' e)).
intros. rename x into xe. rename x' into xe'. destruct xe. apply (is4 y t xe' x). Defined.



Theorem isofhlevelinfibseq (n:nat)(X Y:UU)(f:X -> Y): isofhlevelf n _ _ f -> isofhlevel n Y -> isofhlevel n X.
Proof. intro. induction n.  intros.  apply (iscontrxifiscontry _ _ f X0 X1). intros. simpl.
assert (is1: forall (y:Y)(xe xe': hfiber _ _ f y), isofhlevel n (paths _ xe xe')). intros. apply (X0 y). 
assert (is2: forall (y:Y)(x:X)(xe': hfiber _ _ f y), isofhlevelf n _ _ (d3f _ _ f y x xe')). intros. unfold isofhlevel. intro.
apply (isofhlevelweqf n _ _ _ (isfibseq4 _ _ f y x xe' y0) (is1 y (hfiberpair _ _ f y x y0) xe')). 
assert (is3: forall (y' y : Y), isofhlevel n (paths _ y' y)). simpl in X1. assumption.
intros. rename x into x0. rename x' into x. rename x0 into x'.   
set (y:= f x').  set (e':= idpath _ y). set (xe':= hfiberpair _ _ f y x' e').
apply (IHn _ _ (d3f _ _ f y x xe') (is2 y x xe') (is3 (f x) y)). Defined. 



Theorem isofhlevelfd1f (n:nat)(X Y:UU)(f:X -> Y)(y:Y): (forall y':Y, isofhlevel n (paths _  y' y)) -> isofhlevelf n _ _ (d1f _ _ f y).
Proof.  intros.  unfold isofhlevelf. intro. rename y0 into x. 
apply (isofhlevelweqf n _ _ _ (isfibseq2 _ _ f y x) (X0 (f x))). Defined.





Theorem isofhlevelfsnd1f (n:nat)(X Y:UU)(f:X -> Y)(y:Y): isofhlevel (S n) (paths _  y y) -> isofhlevelf (S n) _ _ (d1f _ _ f y).
Proof.  intros.  unfold isofhlevelf. intro. rename y0 into x. 
assert (is1: paths _ (f x) y -> isofhlevel (S n) (paths _ (f x) y)). intro. destruct X1.  assumption.
assert (is2: isofhlevel (S n) (paths _ (f x) y)). apply isofhlevelsn. assumption.  
apply (isofhlevelweqf (S n) _ _ _ (isfibseq2 _ _ f y x) is2). Defined.



Theorem isofhlevelff (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y -> Z): isofhlevelf n _ _ (fun x:X => g(f x)) -> isofhlevelf (S n) _ _ g -> isofhlevelf n _ _ f.
Proof. intros. unfold isofhlevelf. intro. set (ye:= hfiberpair _ _ g (g y) y (idpath _ (g y))). 
apply (isofhlevelweqb n _ _ _ (isfibseqhfibers _ _ _ f g (g y) ye) (isofhlevelfinfibseq n _ _ _ (X0 (g y)) (X1 (g y)) ye)). Defined.


Theorem isofhlevelfgf (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y -> Z): isofhlevelf n _ _ f -> isofhlevelf n _ _ g -> isofhlevelf n _ _ (fun x:X => g(f x)).
Proof. intros.  unfold isofhlevelf. intro. rename y into z.
assert (is1: isofhlevelf n _ _ (hfibersgftog _ _ _ f g z)). unfold isofhlevelf. intro. rename y into ye. apply (isofhlevelweqf n _ _ _ (isfibseqhfibers _ _ _ f g z ye) (X0 (pr21 _ _ ye))). 
assert (is2: isofhlevel n (hfiber _ _ g z)). apply (X1 z).
apply (isofhlevelinfibseq n _ _ _ is1 is2). Defined.


Corollary isofhlevelffib (n:nat)(X:UU)(P:X -> UU)(x:X): (forall x':X, isofhlevel n (paths _ x' x)) -> isofhlevelf n _ _ (fun p: P x => tpair X P x p).
Proof. intros. unfold isofhlevelf. intro. set (f:= fibmap1 _ P x). set (g:= fun p: P x => tpair X P x p).  rename y into xp. set (pr21x:= pr21 X P).
assert (is1: isofhlevelf n _ _ (d1f _ _ (pr21 X P) x)). apply (isofhlevelfd1f n _ X (pr21 X P) x X0).
assert (h: forall p: P x, paths _ (d1f _ _ pr21x x (f p)) (g p)). intro. apply idpath. 
assert (is2: isofhlevelf n _ _ (fun p: P x => (d1f _ _ pr21x x (f p)))). apply (isofhlevelfgf n _ _ _ f (d1f _ _ pr21x x) (isofhlevelfweq n _ _ f (isweqfibmap1 _ _ x)) is1).  apply (isofhlevelfhomot n _ _ _ _ h is2 xp). Defined. 


Corollary isofhlevelfsnfib (n:nat)(X:UU)(P:X -> UU)(x:X): isofhlevel (S n) (paths _ x x) -> isofhlevelf (S n) _ _ (fun p: P x => tpair X P x p).
Proof. intros. unfold isofhlevelf.    intro.   set (f:= fibmap1 _ P x). set (g:= fun p: P x => tpair X P x p).  rename y into xp. set (pr21x:= pr21 X P).
assert (is1: isofhlevelf (S n) _ _ (d1f _ _ (pr21 X P) x)). apply (isofhlevelfsnd1f n _ X (pr21 X P) x X0). 
assert (h: forall p: P x, paths _ (d1f _ _ pr21x x (f p)) (g p)). intro. apply idpath. 
assert (is2: isofhlevelf (S n) _ _ (fun p: P x => (d1f _ _ pr21x x (f p)))). apply (isofhlevelfgf (S n) _ _ _ f (d1f _ _ pr21x x) (isofhlevelfweq (S n) _ _ f (isweqfibmap1 _ _ x)) is1).  apply (isofhlevelfhomot (S n) _ _ _ _ h is2 xp). Defined.



Theorem isofhlevelfg (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y-> Z): isweq _ _ f -> isofhlevelf n _ _ (fun x:X => g (f x)) -> isofhlevelf n _ _ g.
Proof. intros. set (gf:= fun x:X => g (f x)). set (finv:= invmap _ _ f X0). 
assert (h:forall y:Y, paths _ (gf (finv y)) (g y)). intro. apply (maponpaths _ _ g _ _ (weqfg _ _ f X0 y)).  
assert (is: isofhlevelf n _ _ (fun y:Y => gf (finv y))). apply (isofhlevelfgf n _ _ _ finv gf (isofhlevelfweq n _ _ _ (isweqinvmap _ _ f X0)) X1).  apply (isofhlevelfhomot n _ _ _ _ h is).  Defined.



Corollary isofhlevelfhomot2 (n:nat)(X X' Y:UU)(f:X -> Y)(f':X' -> Y)(w:X -> X')(h:forall x:X, paths _ (f x) (f' (w x)))(is: isweq _ _ w): isofhlevelf n _ _ f -> isofhlevelf n _ _ f'.  
Proof. intros.  assert (isofhlevelf n _ _ (fun x:X => f' (w x))). apply (isofhlevelfhomot n _ _ f (fun x:X => f' (w x)) h X0). 
apply (isofhlevelfg n _ _ _ w f' is X1). Defined.




Theorem isofhlevelfonpaths (n:nat)(X Y:UU)(f:X -> Y)(x x':X): isofhlevelf (S n) _ _ f -> isofhlevelf n _ _ (maponpaths _ _ f x x').
Proof. intros. 
set (y:= f x'). set (xe':= hfiberpair _ _ f y x' (idpath _ _)). 
assert (is1: isofhlevelf n _ _ (d3f _ _ f y x xe')). unfold isofhlevelf. intro.  apply (isofhlevelweqf n _ _ _ (isfibseq4 _ _ f y x xe' y0) (X0 y (hfiberpair _ _ f y x y0) xe')). 
assert (h: forall ee:paths _ x' x, paths _ (d3f _ _ f y x xe' ee) (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee))). intro.
assert (e0: paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) (idpath _ _ ))  (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) ). induction ee.  simpl.  apply idpath. apply (pathscomp0 _ _ _ _ (d3fhomot _ _ f y x xe' ee) e0). apply (isofhlevelfhomot2 n _ _ _ _ _ (pathsinv0 _ x' x) h (isweqpathsinv0 _ _ _) is1) . Defined. 



Theorem isofhlevelfsn (n:nat)(X Y:UU)(f:X -> Y): (forall x x':X, isofhlevelf n _ _ (maponpaths _ _ f x x')) -> isofhlevelf (S n) _ _ f.
Proof. intros.  unfold isofhlevelf. intro.  simpl.  intros. destruct x. rename x into e. rename t into x. destruct x'.  rename t into x'. rename x0 into e'. set (xe':= hfiberpair _ _ f y x' e').  set (xe:= hfiberpair _ _ f y x e). set (d3:= d3f _ _ f y x xe'). simpl in d3.  
assert (is1: isofhlevelf n _ _ (d3f _ _ f y x xe')). 
assert (h: forall ee: paths _ x' x, paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) e') (d3f _ _ f y x xe' ee)). intro. apply (pathsinv0 _ _ _ (d3fhomot _ _ f y x xe' ee)). 
assert (is2: isofhlevelf n _ _ (fun ee: paths _ x' x => maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee))).  apply (isofhlevelfgf n _ _ _ (fun ee:_ => pathsinv0 _ x' x ee) (maponpaths _ _ f x x') (isofhlevelfweq n _ _ _ (isweqpathsinv0 _ _ _)) (X0 x x')). 
assert (is3: isofhlevelf n _ _ (fun ee: paths _ x' x => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) e')). apply (isofhlevelfgf n _ _ _ _ _ is2 (isofhlevelfweq n _ _ _ (isweqpathscomp0r _ _ _ _ e'))). 
apply (isofhlevelfhomot n _ _ _ _ h is3). 
apply (isofhlevelweqb n _ _ _ (isfibseq4 _ _ f y x xe' e) (is1 e)).  Defined.


Theorem isofhlevelfssn (n:nat)(X Y:UU)(f:X -> Y): (forall x:X, isofhlevelf (S n) _ _ (maponpaths _ _ f x x)) -> isofhlevelf (S (S n)) _ _ f.
Proof.  intros.  unfold isofhlevelf. intro.
assert (forall xe0: hfiber _ _ f y, isofhlevel (S n) (paths _ xe0 xe0)). intro. destruct xe0.  rename x into e. rename t into x. set (x':= x). set (e':=e).  set (xe':= hfiberpair _ _ f y x' e').  set (xe:= hfiberpair _ _ f y x e). set (d3:= d3f _ _ f y x xe'). simpl in d3.  
assert (is1: isofhlevelf (S n) _ _ (d3f _ _ f y x xe')). 
assert (h: forall ee: paths _ x' x, paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) e') (d3f _ _ f y x xe' ee)). intro. apply (pathsinv0 _ _ _ (d3fhomot _ _ f y x xe' ee)). 
assert (is2: isofhlevelf (S n) _ _ (fun ee: paths _ x' x => maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee))).  apply (isofhlevelfgf (S n) _ _ _ (fun ee:_ => pathsinv0 _ x' x ee) (maponpaths _ _ f x x') (isofhlevelfweq (S n) _ _ _ (isweqpathsinv0 _ _ _)) (X0 x)). 
assert (is3: isofhlevelf (S n) _ _ (fun ee: paths _ x' x => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ _ ee)) e')). apply (isofhlevelfgf (S n) _ _ _ _ _ is2 (isofhlevelfweq (S n) _ _ _ (isweqpathscomp0r _ _ _ _ e'))). 
apply (isofhlevelfhomot (S n) _ _ _ _ h is3). 
apply (isofhlevelweqb (S n) _ _ _ (isfibseq4 _ _ f y x xe' e) (is1 e)).  
apply (isofhlevelssn).  assumption. Defined.





(** Theorem saying that if each member of a family is of h-level n and so is the base then the total space is of h-level n. *)

Theorem isofhleveltotal2 (n:nat)(X:UU)(P:X -> UU)(is1: isofhlevel n X)(is2: forall x:X, isofhlevel n (P x)): isofhlevel n (total2 X P).
Proof. intros. apply (isofhlevelinfibseq n (total2 X P) X (pr21 _ _)). apply isofhlevelfpr21. assumption. assumption. Defined. 

Corollary isofhleveldirprod (n:nat)(X Y:UU)(is1:isofhlevel n X)(is2: isofhlevel n Y): isofhlevel n (dirprod X Y).
Proof. intros. apply isofhleveltotal2. assumption. intro. assumption. Defined. 




(** Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

Theorem impred (n:nat)(T:UU)(P:T -> UU): (forall t:T, isofhlevel n (P t)) -> (isofhlevel n (forall t:T, P t)).
Proof. intro. induction n. intros.  apply (funcontr T P X). intros. unfold isofhlevel in X.  unfold isofhlevel. intros. 

assert (is: forall t:T, isofhlevel n (paths _ (x t) (x' t))).  intro. apply (X t (x t) (x' t)).  
assert (is2: isofhlevel n (forall t:T, paths _ (x t) (x' t))). apply (IHn _ (fun t0:T => paths _ (x t0) (x' t0)) is).
set (u:=funextmap _ P x x').  assert (is3:isweq _ _ u). apply isweqfunextmap.  set (v:= invmap _ _ u is3). assert (is4: isweq _ _ v). apply isweqinvmap. apply (isofhlevelweqf n _ _ v is4). assumption. Defined.

Corollary impredtwice  (n:nat)(T T':UU)(P:T -> T' -> UU): (forall (t:T)(t':T'), isofhlevel n (P t t')) -> (isofhlevel n (forall (t:T)(t':T'), P t t')).
Proof.  intros. assert (is1: forall t:T, isofhlevel n (forall t':T', P t t')). intro. apply (impred n _ _ (X t)). apply (impred n _ _ is1). Defined.


Corollary impredfun (n:nat)(X Y:UU)(is: isofhlevel n Y) : isofhlevel n (X -> Y).
Proof. intros. apply (impred n X (fun x:_ => Y) (fun x:X => is)). Defined. 


Theorem impredtech1 (n:nat)(X Y: UU) : (X -> isofhlevel n Y) -> isofhlevel n (X -> Y).
Proof. intro. induction n. intros. simpl. split with (fun x:X => pr21 _ _ (X0 x)).  intro. 
assert (s1: forall x:X, paths _ (t x) (pr21 _ _ (X0 x))). intro. apply contrl2. apply (X0 x). 
apply funextsec. assumption. 

intros. simpl. assert (X1: X -> isofhlevel (S n) (X -> Y)). intro. apply impred. assumption. intros.
assert (s1: isofhlevel n (forall xx:X, paths _ (x xx) (x' xx))). apply impred. intro. apply (X0 t). 
assert (w: weq (forall xx:X, paths Y (x xx) (x' xx)) (paths (X->Y) x x')). apply (weqinv _ _ (weqfunextsec _ _ _ _ )). apply (isofhlevelweqf n _ _ (pr21 _ _ w) (pr22 _ _ w) s1). Defined. 















(** ** Fibrations with only one non-empty fiber. 

Theorem saying that if a fibration has only one non-empty fiber then the total space is weakly equivalent to this fiber. *)



Theorem onefiber (X:UU)(P:X -> UU)(x:X)(c: forall x':X, coprod (paths _ x x') (P x' -> empty)):
isweq _ _ (fun p: P x => tpair X P x p).
Proof. intros.  

set (f:= fun p: P x => tpair _ _ x p). 

set (cx := c x). 
set (cnew:=  fun x':X  =>
match cx with 
ii1 x0 =>
match c x' with 
ii1 ee => ii1 _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ x0) ee)|
ii2 phi => ii2 _ _ phi
end |
ii2 phi => c x'
end).

set (g:= fun pp: total2 X P => 
match (cnew (pr21 _ _ pp)) with
ii1 e => transportb X P _ _ e (pr22 _ _ pp) |
ii2 phi =>  initmap _ (phi (pr22 _ _ pp))
end).


assert (efg: forall pp: total2 X P, paths _ (f (g pp)) pp).  intro. induction pp. set (cnewt:= cnew t).  unfold g. unfold f. simpl. change (cnew t) with cnewt. induction cnewt.  apply (pathsinv0 _ _ _ (pr21 _ _ (pr22 _ _ (constr1 X P t x (pathsinv0 _ _ _ x1))) x0)). induction (y x0). 

 
set (cnewx:= cnew x). 
assert (e1: paths _ (cnew x) cnewx). apply idpath. 
unfold cnew in cnewx. change (c x) with cx in cnewx.  
induction cx.  
assert (e: paths _ (cnewx) (ii1 _ _ (idpath _ x))).  apply (maponpaths _ _ (ii1 (paths X x x) (P x -> empty)) _ _ (pathsinv0l1 _ _ _ x0)). 




assert (egf: forall p: P x, paths _ (g (f p)) p).  intro. simpl in g. unfold g.  unfold f.   simpl.   

set (ff:= fun cc:coprod (paths X x x) (P x -> empty) => 
match cc with
     | ii1 e0 => transportb X P x x e0 p
     | ii2 phi => initmap (P x) (phi p)
     end).
assert (ee: paths _ (ff (cnewx)) (ff (ii1 (paths X x x) (P x -> empty) (idpath X x)))).  apply (maponpaths _ _ ff _ _ e). 
assert (eee: paths _  (ff (ii1 (paths X x x) (P x -> empty) (idpath X x))) p). apply idpath.  fold (ff (cnew x)). 
assert (e2: paths _ (ff (cnew x)) (ff cnewx)). apply (maponpaths _ _ ff _ _ e1). 
apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e2 ee) eee).
apply (gradth _ _ f g egf efg).

unfold isweq.  intro. induction (y (g y0)). Defined.









(** * Propositions, inclusions  and sets. *)







(** ** Basics about types of h-level 1 - "propositions". *)


Definition isaprop (X:UU): UU := isofhlevel (S O) X. 

Lemma isweqimplimpl (X:UU)(Y:UU)(f:X->Y)(g:Y->X)(isx: isaprop X)(isy: isaprop Y): isweq _ _ f.
Proof. intros. assert (isx0: forall x:X, paths _ (g (f x)) x). intro.  assert (iscontr X). apply (iscontraprop1 X isx x).  apply (contrl2 X X0 (g (f x)) x). assert (isy0: forall y:Y, paths _ (f (g y)) y). intro. assert (iscontr Y). apply (iscontraprop1 Y isy y). apply (contrl2 Y X0 (f (g y)) y). apply (gradth _ _ f g isx0 isy0).  Defined. 

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros. induction x. Defined. 


Lemma proofirrelevance (X:UU): (isaprop X) -> (forall (x x':X), paths _ x x'). 
Proof. intros. unfold isaprop in X0. unfold isofhlevel in X0.   apply (pr21 _ _ (X0 x x')). Defined. 


Lemma invproofirrelevance (X:UU): (forall (x x':X), paths _ x x') -> isaprop X.
Proof. intros. unfold isaprop. unfold isofhlevel.  intro.  
assert (is: iscontr X).  split with x. intro.  apply (X0 t x). assert (is1: isaprop X).  apply isapropifcontr. assumption.   
unfold isaprop in is1. unfold isofhlevel in is1.  apply (is1 x). Defined. 


Lemma isapropifnegtrue (X:UU): neg X -> isaprop X.
Proof. intros. assert (is:isweq _ _ X0). intro. apply (initmap _ y).   apply (isofhlevelweqb (S O) _ _ _ is isapropempty). Defined. 



Definition isdecprop (X:UU):= dirprod (isaprop X) (coprod X (X -> empty)).





(** ** Theorems saying that  (iscontr T), (isweq f) etc. are of h-level 1. *)



Theorem iscontriscontr: forall X:UU, iscontr(X)->iscontr(iscontr(X)).
Proof. intros. 

assert (is0: forall (x x':X), paths _ x x'). apply contrl2. assumption.

assert (is1: forall cntr:X, iscontr (forall x:X, paths _ x cntr)). intro. 
assert (is2: forall x:X, iscontr (paths _ x cntr)). 
assert (is2: isaprop X). apply isapropifcontr. assumption.  
unfold isaprop in is2. unfold isofhlevel in is2. intro. apply (is2 x cntr).
apply funcontr. assumption. 

set (f:= pr21 X (fun cntr:X => forall x:X, paths _ x cntr)). 
assert (isweq _ _ f).  apply trivfib1. assumption. change (total2 X (fun cntr : X => forall x : X, paths X x cntr)) with (iscontr X) in X1.  apply (iscontrxifiscontry _ _ f X1). assumption.  Defined. 



Theorem isapropiscontr (T:UU): isaprop (iscontr T).
Proof. intros.  unfold isaprop.  unfold isofhlevel. intros. assert (is: iscontr(iscontr T)). apply iscontriscontr. apply x. assert (is2: isaprop (iscontr T)). apply (isapropifcontr _ is). apply (is2 x x'). Defined.  



Theorem isapropisweq (X:UU)(Y:UU)(f:X-> Y) : isaprop (isweq _ _ f).
Proof. intros. unfold isweq.  apply (impred (S O) _ (fun y:Y => iscontr (hfiber X Y f y)) (fun y:Y => isapropiscontr (hfiber X Y f y))).  Defined. 


Theorem isapropisofhlevel (n:nat)(X:UU): isaprop (isofhlevel n X).
Proof. intro.  unfold isofhlevel.    induction n. apply isapropiscontr.  intro. 
assert (forall (x x':X), isaprop  ((fix isofhlevel (n0 : nat) (X0 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X0
         | S m => forall x0 x'0 : X0, isofhlevel m (paths X0 x0 x'0)
         end) n (paths X x x'))). intros. apply (IHn (paths _ x x')). 
assert (is1: 
     (forall x:X, isaprop (forall  x' : X,
      (fix isofhlevel (n0 : nat) (X1 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X1
         | S m => forall x0 x'0 : X1, isofhlevel m (paths X1 x0 x'0)
         end) n (paths X x x')))). intro.  apply (impred (S O) _ _ (X0 x)). apply (impred (S O) _ _ is1). Defined. 

Corollary isapropisaprop (X:UU) : isaprop (isaprop X).
Proof. intro. apply (isapropisofhlevel (S O)). Defined. 





(** ** More results on types of h-level 1 (propositions). *)



Theorem isapropneg (X:UU): isaprop (X -> empty).
Proof. intro. apply (impredfun (S O) X empty isapropempty). Qed.

Corollary isapropdneg (X:UU): isaprop (dneg X).
Proof. intro. apply (isapropneg (neg X)). Defined.


Definition isaninvprop (X:UU):= isweq _ _  (todneg X).

Definition invimpl (X:UU)(is: isaninvprop X): (dneg X) -> X:= invmap _ _ (todneg X) is. 


Lemma isapropaninvprop (X:UU): isaninvprop X -> isaprop X.
Proof. intros. 
apply (isofhlevelweqb (S O) _ _ (todneg X) X0 (isapropdneg X)). Defined. 


Theorem isaninvpropneg (X:UU): isaninvprop (neg X).
Proof. intros. 
set (f:= todneg (neg X)). set (g:= negf _ _ (todneg X)). set (is1:= isapropneg X). set (is2:= isapropneg (dneg X)). apply (isweqimplimpl _ _ f g is1 is2).  Defined.


Theorem isapropisdec (X:UU): (isaprop X) -> (isaprop (coprod X (X-> empty))).
Proof. intros. 
assert (forall (x x': X), paths _ x x'). apply (proofirrelevance _ X0).  
assert (forall (x x': coprod X (X -> empty)), paths _ x x'). intros.  
induction x.  induction x'.   apply (maponpaths _ _ (fun x:X => ii1 _ _ x) _ _ (X1 x x0)).    
apply (initmap _ (y x)). induction x'.   apply (initmap _ (y x)). 
assert (e: paths _ y y0). apply (proofirrelevance _ (isapropneg X) y y0). apply (maponpaths _ _ (fun f: X -> empty => ii2 _ _ f) _ _ e).
apply (invproofirrelevance _ X2).  Defined. 


Theorem isaninv1 (X:UU): isdecprop X  -> isaninvprop X.
Proof. unfold isaninvprop. intros. rename X0 into is.  set (is1:= pr21 _ _ is). set (is2:= pr22 _ _ is). simpl in is2. 
assert (adjevinv: dneg X -> X). intros.  induction is2.  assumption. induction (X0 y). 
assert (is3: isaprop (dneg X)). apply (isapropneg (X -> empty)). apply (isweqimplimpl _ _ (todneg X) adjevinv is1 is3). Defined. 







(** ** Basics about functions of h-level 1 (inclusions). *)


Definition isincl (X Y:UU)(f:X -> Y):= isofhlevelf (S O) _ _ f.

Lemma iscontrhfiberofincl (X:UU)(Y:UU)(f:X -> Y): isincl _ _ f -> (forall x:X, iscontr (hfiber _ _ f (f x))).
Proof. intros. unfold isofhlevelf in X0. set (isy:= X0 (f x)).  apply (iscontraprop1 _ isy (hfiberpair _ _ f (f x) x (idpath _ (f x)))). Defined.


Lemma isweqonpathsincl (X:UU)(Y:UU)(f:X -> Y)(is: isincl _ _ f)(x x':X): isweq _ _ (maponpaths _ _ f x x').
Proof. intros. apply (isofhlevelfonpaths O _ _ f x x' is). Defined.


Definition invmaponpathsincl (X Y:UU)(f:X -> Y) (is: isincl _ _ f)(x x':X): paths _ (f x) (f x') -> paths _ x x':= invmap _ _ (maponpaths _ _ f x x') (isweqonpathsincl _ _ f is x x').


Lemma isinclweqonpaths (X Y:UU)(f:X -> Y): (forall x x':X, isweq _ _ (maponpaths _ _ f x x')) -> isincl _ _ f.
Proof. intros.  apply (isofhlevelfsn O _ _ f X0). Defined.












(** ** Basics about types of h-level 2 - "sets". *)




Definition isaset (X:UU): UU := isofhlevel (S (S O)) X. 


Corollary isapropisaset (X:UU): isaprop (isaset X).
Proof. intro. apply (isapropisofhlevel (S (S O))). Defined.


Lemma isaset1 (X:UU): (forall x:X, iscontr (paths _ x x)) -> isaset X.
Proof. intros. unfold isaset. unfold isofhlevel. intros.   induction x0. set (is:= X0 x). apply isapropifcontr. assumption.  Defined. 

Lemma isaset2 (X:UU): (isaset X) -> (forall x:X, iscontr (paths _ x x)).
Proof. intros. unfold isaset in X0. unfold isofhlevel in X0.  change (forall (x x' : X) (x0 x'0 : paths X x x'), iscontr (paths (paths X x x') x0 x'0))  with (forall (x x':X),  isaprop (paths _ x x')) in X0.  apply (iscontraprop1 _ (X0 x x) (idpath _ x)). Defined.












(** * Coprojections, isolated points and types with decidable equality. *)


(** ** Types with decidable equality are of h-level 2 (i.e. sets). *)




Definition isdeceq (X:UU): UU :=  forall (x x':X), coprod (paths _ x' x) (paths _ x' x -> empty).


Lemma dnegdec (X:UU): dneg (coprod X (neg X)).
Proof. intros. intro.   set (a:= fun x:X => X0 (ii1 _ _ x)). set (b:= fun x:neg X => X0 (ii2 _ _ x)). apply (b a). Defined. 


Theorem isasetifdeceq (X:UU): (isdeceq X) -> isaset X.
Proof. intro. intro. unfold isdeceq in X0.  
assert (l1: forall x:X, iscontr (paths _ x x)). intro.  set (f:= fun e: paths _ x x => coconusfromtpair _ x x e). 
assert (is: isweq _ _ f). apply (onefiber X (fun x':X => paths _ x x') x (fun x':X => X0 x' x)).
assert (is2: iscontr (coconusfromt _ x)). apply iscontrcoconusfromt. 
apply (iscontrxifiscontry _ _ f is). assumption. apply isaset1. assumption. Defined. 




Theorem isapropisdeceq (X:UU): isaprop (isdeceq X).
Proof. intro. unfold isdeceq.
assert (forall u u':isdeceq X, paths _ u u'). intros. 
assert (forall x x':X, isaprop (coprod (paths X x x') (paths X x x' -> empty))). intros.  assert (is0:isaprop (paths _ x x')). assert (is1: isaset X). apply (isasetifdeceq _ u).  set (is2:= is1 x x'). simpl in is2. unfold isaprop. unfold isofhlevel. assumption. 
apply (isapropisdec _ is0). assert (isaprop (isdeceq X)). apply impredtwice. intros.  apply (X0 t' t). apply (proofirrelevance _ X1 u u'). apply (invproofirrelevance _ X0). Defined.
   


Corollary eqfromdnegeq (X:UU)(is: isdeceq X)(x x':X): dneg( paths _ x x') -> paths _ x x'.
Proof. intros. set (a:= dirprodpair (isaprop (paths _ x x')) (coprod (paths _ x x') (paths _ x x' -> empty)) (isasetifdeceq X is x x') (is x' x)). set (isinv:= isaninv1 _ a). apply (invimpl _ isinv X0). Defined. 





Fixpoint curry (x:bool) : UU := 
match x with
false => empty|
true => unit
end.



Theorem nopathstruetofalse: paths _ true false -> empty.
Proof. intro.  apply (transportf _ curry _ _ X tt).  Defined.

Corollary nopathsfalsetotrue: paths _ false true -> empty.
Proof. intro. apply (transportb _ curry _ _ X tt). Defined. 

Theorem isdeceqbool: isdeceq bool.
Proof. unfold isdeceq. intros. induction x. induction x'. apply (ii1 _ _ (idpath _ true)). apply (ii2 _ _ nopathsfalsetotrue). induction x'.  apply (ii2 _ _ nopathstruetofalse). apply (ii1 _ _ (idpath _ false)). Defined. 


Theorem isasetbool: isaset bool.
Proof. apply (isasetifdeceq _ isdeceqbool). Defined. 


Lemma noneql1 (X Y: UU)(f:X -> Y)(x x':X): (paths _ (f x) (f x') -> empty) -> (paths _ x x' -> empty).
Proof. intros. apply (X0 (maponpaths _ _ f _ _ X1)). Defined.  


Theorem nopathsOtoSx: forall x:nat, paths _ O (S x) -> empty.
Proof. intro. 
set (f:= fun n:nat => match n with 
O => true|
S m => false
end). 

apply (noneql1 _ _ f O (S x) nopathstruetofalse). Defined. 

Corollary nopathsSxtoO: forall x:nat, paths _ (S x) O -> empty.
Proof. intros. apply (nopathsOtoSx x (pathsinv0 _ _ _ X)). Defined. 

Lemma noeqinjS: forall (x x':nat),  (paths _ x x' -> empty) -> (paths _ (S x) (S x') -> empty).
Proof. set (f:= fun n:nat => match n with 
O => O|
S m => m
end). 

intro. intro. intro. apply (noneql1 _ _ f (S x) (S x') X). Defined. 
 

Theorem isdeceqnat: isdeceq nat.
Proof. unfold isdeceq.  intro. induction x. intro. destruct x'. apply (ii1 _ _ (idpath _ O)). apply (ii2 _ _ (nopathsSxtoO x')). intro.  destruct x'.  apply (ii2 _ _ (nopathsOtoSx x)). destruct (IHx x').   apply (ii1 _ _ (maponpaths _ _ S _ _ p)).  apply (ii2 _ _ (noeqinjS _ _  e)). Defined. 



Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdeceq _ isdeceqnat). Defined. 






(** ** More on pairwise coproducts. *)


Definition coprodtobool (X Y:UU): coprod X Y -> bool:= fun xy:_ =>
match xy with
ii1 x => true|
ii2 y => false
end.
 

Definition boolsumfun (X Y:UU): bool -> UU := fun t:_ => 
match t with
true => X|
false => Y
end.

Definition coprodtoboolsum (X Y:UU): (coprod X Y) -> (total2 bool (boolsumfun X Y)):=  (fun xy: coprod X Y =>
match xy with
ii1 x => tpair _ (boolsumfun X Y) true x|
ii2 y => tpair _ (boolsumfun X Y) false y
end).


Definition boolsumtocoprod (X Y:UU): (total2 bool (boolsumfun X Y)) -> coprod X Y := (fun xy:_ =>
match xy with 
tpair true x => ii1 _ _ x|
tpair false y => ii2 _ _ y
end).



Theorem isweqcoprodtoboolsum (X Y:UU): isweq _ _ (coprodtoboolsum X Y).
Proof. intros. set (f:= coprodtoboolsum X Y). set (g:= boolsumtocoprod X Y). 
assert (egf: forall xy: coprod X Y , paths _ (g (f xy)) xy). destruct xy. apply idpath. apply idpath. 
assert (efg: forall xy: total2 bool (boolsumfun X Y), paths _ (f (g xy)) xy). intro. destruct xy. destruct t.  apply idpath. apply idpath. apply (gradth _ _ f g egf efg). Defined.

Corollary isweqboolsumtocoprod (X Y:UU): isweq _ _ (boolsumtocoprod X Y ).
Proof. intros. apply (isweqinvmap _ _ _ (isweqcoprodtoboolsum X Y)). Defined.






Theorem isinclii1 (X Y:UU): isincl _ _ (ii1 X Y).
Proof. intros. set (f:= ii1 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun x:X => (g (f x))). set (gf':= fun x:X => tpair _ (boolsumfun X Y) true x). 
assert (h: forall x:X , paths _ (gf' x) (gf x)). intro. apply idpath. 
assert (is1: isofhlevelf (S O) _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) true (isasetbool true true)).
assert (is2: isofhlevelf (S O) _ _ gf). apply (isofhlevelfhomot (S O) _ _ gf' gf h is1).  
apply (isofhlevelff (S O) _ _ _ _ _ is2 (isofhlevelfweq (S (S O)) _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 


Theorem isinclii2 (X Y:UU): isincl _ _ (ii2 X Y).
Proof. intros. set (f:= ii2 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun y:Y => (g (f y))). set (gf':= fun y:Y => tpair _ (boolsumfun X Y) false y). 
assert (h: forall y:Y , paths _ (gf' y) (gf y)). intro. apply idpath. 
assert (is1: isofhlevelf (S O) _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) false (isasetbool false false)).
assert (is2: isofhlevelf (S O) _ _ gf). apply (isofhlevelfhomot (S O) _ _ gf' gf h is1).  
apply (isofhlevelff (S O) _ _ _ _ _ is2 (isofhlevelfweq (S (S O)) _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 




Lemma negintersectii1ii2 (X Y:UU)(z: coprod X Y): hfiber _ _ (ii1 X Y) z -> hfiber _ _ (ii2 _ _) z -> empty.
Proof. intros. destruct X0. destruct X1.  
set (e:= pathscomp0 _ _ _ _ x (pathsinv0 _ _ _ x0)). apply (negpathsii1ii2 _ _ _ _ e). Defined. 

Definition coprodsplit {X Y Z:UU}(f:X -> coprod Y Z): coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z)) -> X := 
sumofmaps (hfppr1 f (ii1 Y Z)) (hfppr1 f (ii2 Y Z)).


Definition coprodsplitinv {X Y Z:UU}(f:X -> coprod Y Z): X -> coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z)).
Proof. intros. set (fx0:= f X0). unfold hfp.
assert (int1: coprod (hfiber _ _ (ii1 Y Z) fx0) (hfiber _ _ (ii2 Y Z) fx0)). destruct fx0. apply (ii1 _ _ (hfiberpair _ _ _ (ii1 _ _ y) y (idpath _ _))). apply (ii2 _ _ (hfiberpair _ _ _ (ii2 _ _ z) z (idpath _ _))). 
apply (coprodf _ _ _ _ (hfppair f _ X0) (hfppair f _ X0) int1). Defined.


Theorem weqcoprodsplit {X Y Z:UU}(f:X -> coprod Y Z): weq (coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z))) X.
Proof. intros. set (ff:= coprodsplit f). split with ff. set (gg:= coprodsplitinv f).
assert (egf: forall x:_, paths _ (gg (ff x)) x). intro. destruct x. simpl. destruct h.  simpl. unfold gg. unfold coprodsplitinv. 

set (int1:= match
          f t as c
          return
            (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
               (hfiber Z (coprod Y Z) (ii2 Y Z) c))
        with
        | ii1 y =>
            ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
              (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                 (ii1 Y Z y) y (idpath (coprod Y Z) (ii1 Y Z y)))
        | ii2 z =>
            ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
              (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                 (ii2 Y Z z) z (idpath (coprod Y Z) (ii2 Y Z z)))
        end). destruct int1.  simpl. assert (e: paths _ h x). apply (proofirrelevance _ (isinclii1 _ _ (f t))).   induction e.  apply idpath. 
simpl. apply (initmap _ (negintersectii1ii2 _ _ (f t) x h)). 


simpl. destruct h.  simpl. unfold gg. unfold coprodsplitinv. 

set (int1:= match
          f t as c
          return
            (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
               (hfiber Z (coprod Y Z) (ii2 Y Z) c))
        with
        | ii1 y =>
            ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
              (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                 (ii1 Y Z y) y (idpath (coprod Y Z) (ii1 Y Z y)))
        | ii2 z =>
            ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
              (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                 (ii2 Y Z z) z (idpath (coprod Y Z) (ii2 Y Z z)))
        end). destruct int1. apply (initmap _ (negintersectii1ii2 _ _ (f t) h x)).  simpl. assert (e: paths _ h x). apply (proofirrelevance _ (isinclii2 _ _ (f t))).   induction e.  apply idpath. 

assert (efg: forall x:_, paths _ (ff (gg x)) x). intro. unfold gg. unfold coprodsplitinv.  

set (int1:= match
             f x as c
             return
               (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
                  (hfiber Z (coprod Y Z) (ii2 Y Z) c))
           with
           | ii1 y =>
               ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
                 (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
                 (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                    (ii1 Y Z y) y (idpath (coprod Y Z) (ii1 Y Z y)))
           | ii2 z =>
               ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
                 (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
                 (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                    (ii2 Y Z z) z (idpath (coprod Y Z) (ii2 Y Z z)))
           end). destruct int1.  simpl. apply idpath.  simpl. apply idpath.

apply (gradth _ _ ff gg egf efg). Defined. 


Definition subsetsplit (X:UU)(f:X -> bool): (coprod (hfiber _ _ f true) (hfiber _ _ f false)) -> X := fun ab:_ => match ab with ii1 xt => pr21 _ _ xt | ii2 xf => pr21 _ _ xf end.


Theorem weqsubsetsplit (X:UU)(f:X -> bool): weq (coprod (hfiber _ _ f true) (hfiber _ _ f false))  X.
Proof.  intros.  set (g:= pr21 _ _ (weqinv _ _ boolascoprod)). 
assert (et: paths _ (ii1 _ _ tt) (g true)). apply idpath. 
assert (ef: paths _ (ii2 _ _ tt) (g false)). apply idpath. 
set (gf:= fun x:X => g (f (x))). set (w1:= weqcoprodsplit gf). 

assert (w2: weq (hfiber X bool f true) (hfp gf (ii1 unit unit))). unfold hfiber. unfold hfp. 
assert (w2a: forall x:X, weq (paths bool (f x) true) (hfiber unit (coprod unit unit) (ii1 unit unit) (gf x))). intro. set (fx:= f x). change (gf x) with (g fx).  destruct fx. 
assert (is1: iscontr (paths bool true true)). apply (isaset2 _ isasetbool true). 
assert (is2: iscontr (hfiber unit (coprod unit unit) (ii1 unit unit) (g true))). induction et.  apply (iscontrhfiberofincl _ _ (ii1 _ _) (isinclii1 _ _) tt). apply (weqpair _ _ _ (ifcontrcontrthenweq _ _ (fun a:_ => pr21 _ _ is2) is1 is2)). 
assert (is1: weq (paths bool false true) empty). apply (weqpair _ _ _ (isweqtoempty _ nopathsfalsetotrue)). 
assert (is2: neg (hfiber unit (coprod unit unit) (ii1 unit unit) (g false))). destruct ef.  intro.  destruct X0.  apply (negpathsii1ii2 _ _ _ _ x0). apply (weqcomp _ _ _ is1 (weqinv _ _ (weqpair _ _ _ (isweqtoempty _ is2)))). split with (totalfun _ _ _ (fun x:X => pr21 _ _ (w2a x))). apply (isweqfibtototal _ _ _ _ (fun x:X => pr22 _ _ (w2a x))). 

assert (w3: weq (hfiber X bool f false) (hfp gf (ii2 unit unit))). unfold hfiber. unfold hfp. 
assert (w3a: forall x:X, weq (paths bool (f x) false) (hfiber unit (coprod unit unit) (ii2 unit unit) (gf x))). intro. set (fx:= f x). change (gf x) with (g fx).  destruct fx. 

assert (is1: weq (paths bool true false) empty). apply (weqpair _ _ _ (isweqtoempty _ nopathstruetofalse)). 
assert (is2: neg (hfiber unit (coprod unit unit) (ii2 unit unit) (g true))). destruct ef.  intro.  destruct X0.  apply (negpathsii2ii1 _ _ _ _ x0). apply (weqcomp _ _ _ is1 (weqinv _ _ (weqpair _ _ _ (isweqtoempty _ is2)))). 

assert (is1: iscontr (paths bool false false)). apply (isaset2 _ isasetbool false). 
assert (is2: iscontr (hfiber unit (coprod unit unit) (ii2 unit unit) (g false))). induction ef.  apply (iscontrhfiberofincl _ _ (ii2 _ _) (isinclii2 _ _) tt). apply (weqpair _ _ _ (ifcontrcontrthenweq _ _ (fun a:_ => pr21 _ _ is2) is1 is2)). 

split with (totalfun _ _ _ (fun x:X => pr21 _ _ (w3a x))). apply (isweqfibtototal _ _ _ _ (fun x:X => pr22 _ _ (w3a x))). 

apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ w2 w3) w1). Defined. 







Definition fromhfibercoprodf1 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(x':X'):(hfiber _ _ (coprodf _ _ _ _ f g) (ii1 _ _ x')) -> hfiber _ _ f x'.
Proof. intros. destruct X0.  destruct t. set (e:= invmaponpathsincl _ _ _ (isinclii1 X' Y') _ _ x). apply (hfiberpair _ _ _ _ x0 e). apply (initmap _ (negpathsii2ii1 _ _ _ _ x)). Defined. 


Theorem weqhfibercoprodf1 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(x':X'): weq (hfiber _ _ f x') (hfiber _ _ (coprodf _ _ _ _ f g) (ii1 _ _ x')).
Proof. intros.  set (ff:= fun xe: hfiber _ _ f x' => match xe with tpair x e => hfiberpair _ _ (coprodf _ _ _ _ f g) _ (ii1 X Y x) (maponpaths _ _ (ii1 X' Y') (f x) x' e) end). split with ff. set (gg:= fromhfibercoprodf1 _ _ _ _ f g x').
assert (egf: forall a:_, paths _ (gg (ff a)) a).  intro. destruct a.  simpl.  induction x.  simpl. apply idpath. 
assert (efg: forall a:_, paths _ (ff (gg a)) a). intro. destruct a. destruct t.  simpl in x. 
assert (eee: total2 (paths _ (f x0) x') (fun e:_ => paths _ (maponpaths _ _ (ii1 X' Y') _ _ e) x)). split with (invmaponpathsincl _ _ _ (isinclii1 X' Y') _ _ x).  apply (weqfg _ _ _ (isweqonpathsincl _ _ _ (isinclii1 X' Y') _ _ ) x).   destruct eee. induction x1. induction t. apply idpath. 
simpl in x. apply (initmap _ (negpathsii2ii1 _ _ _ _  x)). 
apply (gradth _ _ _ _ egf efg). Defined. 




Definition fromhfibercoprodf2 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(y':Y'):(hfiber _ _ (coprodf _ _ _ _ f g) (ii2 _ _ y')) -> hfiber _ _ g y'.
Proof. intros. destruct X0.  destruct t. apply (initmap _ (negpathsii1ii2 _ _ _ _ x)).  set (e:= invmaponpathsincl _ _ _ (isinclii2 X' Y') _ _ x). apply (hfiberpair _ _ _ _ y e). Defined. 




Theorem weqhfibercoprodf2 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(y':Y'): weq (hfiber _ _ g y') (hfiber _ _ (coprodf _ _ _ _ f g) (ii2 _ _ y')).
Proof. intros.  set (ff:= fun xe: hfiber _ _ g y' => match xe with tpair y e => hfiberpair _ _ (coprodf _ _ _ _ f g) _ (ii2 X Y y) (maponpaths _ _ (ii2 X' Y') (g y) y' e) end). split with ff. set (gg:= fromhfibercoprodf2 _ _ _ _ f g y').
assert (egf: forall a:_, paths _ (gg (ff a)) a).  intro. destruct a.  simpl.  induction x.  simpl. apply idpath. 
assert (efg: forall a:_, paths _ (ff (gg a)) a). intro. destruct a. destruct t.  simpl in x. apply (initmap _ (negpathsii1ii2 _ _ _ _  x)). 
simpl in x. assert (eee: total2 (paths _ (g y) y') (fun e:_ => paths _ (maponpaths _ _ (ii2 X' Y') _ _ e) x)). split with (invmaponpathsincl _ _ _ (isinclii2 X' Y') _ _ x).  apply (weqfg _ _ _ (isweqonpathsincl _ _ _ (isinclii2 X' Y') _ _ ) x).   destruct eee. induction x0. induction t. apply idpath. 
apply (gradth _ _ _ _ egf efg). Defined. 

 






(** Theorem saying that coproduct of two maps of h-level n is of h-level n. *)



Theorem isofhlevelfcoprodf (n:nat)(X Y Z T:UU)(f: X -> Z)(g: Y -> T)(is1: isofhlevelf n _ _ f)(is2: isofhlevelf n _ _ g): isofhlevelf n _ _  (coprodf _ _ _ _ f g).
Proof. intros. intro.  destruct y.  apply (isofhlevelweqf n _ _ _ (pr22 _ _ (weqhfibercoprodf1 _ _ _ _ f g z)) (is1 z)).  apply (isofhlevelweqf n _ _ _ (pr22 _ _ (weqhfibercoprodf2 _ _ _ _ f g t)) (is2 t)). Defined. 



(** Coprojections. *)



Definition isacoproj {X Y:UU}(f :X -> Y)(is: isincl _ _ f):= forall y:Y, coprod (hfiber _ _ f y) (neg (hfiber _ _ f y)). 

Lemma isacoprojii1 (X Y: UU): isacoproj (ii1 _ _) (isinclii1 X Y).
Proof. intros. unfold isacoproj. intro.  destruct y.   apply (ii1 _ _ (hfiberpair _ _ (ii1 _ _ ) (ii1 _ _ x) x (idpath _ _ ))). 
assert (int: (neg (hfiber X (coprod X Y) (ii1 X Y) (ii2 X Y y)))).  intro.  destruct X0.  apply (negpathsii1ii2 _ _ _ _ x). apply (ii2 _ _ int).  Defined.  

 
Lemma isacoprojii2 (X Y: UU): isacoproj (ii2 _ _) (isinclii2 X Y).
Proof. intros. unfold isacoproj. intro.  destruct y.   
assert (int: (neg (hfiber Y (coprod X Y) (ii2 X Y) (ii1 X Y x)))).  intro.  destruct X0.  apply (negpathsii1ii2 _ _ _ _ (pathsinv0 _ _ _ x0)). apply (ii2 _ _ int). apply (ii1 _ _ (hfiberpair _ _ (ii2 _ _ ) (ii2 _ _ y) y (idpath _ _ ))).   Defined.  







(** ** Some results on complements to a point *)


Definition complement (X:UU)(x:X):= total2 X (fun x':X => neg (paths _ x' x)).
Definition complementpair (X:UU)(x:X):= tpair X (fun x':X => neg (paths _ x' x)).


Definition recompl (X:UU)(x:X): coprod (complement X x) unit -> X := fun u:_ =>
match u with
ii1 x0 => pr21 _ _ x0|
ii2 tt => x
end.

Definition maponcomplementsincl (X:UU)(Y:UU)(f:X -> Y)(is: isofhlevelf (S O) _ _ f)(x:X): complement X x -> complement Y (f x):= fun x0':_ =>
match x0' with
tpair x' neqx => tpair _ _ (f x') (negf _ _ (invmaponpathsincl _ _ _ is x' x) neqx)
end.

Definition maponcomplementsweq (X Y:UU)(f:X -> Y)(is: isweq _ _ f)(x:X):= maponcomplementsincl _ _ f (isofhlevelfweq (S O) _ _ f is) x.


Theorem isweqmaponcomplements (X Y:UU)(f:X -> Y)(is: isweq _ _ f)(x:X): isweq _ _ (maponcomplementsweq _ _ f is x).
Proof. intros.  set (is1:= isofhlevelfweq (S O) _ _ f is).   set (map1:= totalfun X (fun x':X => neg (paths _ x' x)) (fun x':X => neg (paths _ (f x') (f x))) (fun x':X => negf _ _ (invmaponpathsincl _ _ _ is1 x' x))). set (map2:= fpmap _ _ f (fun y:Y => neg (paths _ y (f x)))). 
assert (is2: forall x':X, isweq  _ _ (negf _ _ (invmaponpathsincl _ _ _ is1 x' x))). intro. 
set (invimpll:= (negf _ _ (maponpaths _ _ f x' x))). apply (isweqimplimpl _ _ (negf _ _ (invmaponpathsincl _ _ _ is1 x' x)) (negf _ _ (maponpaths _ _ f x' x)) (isapropneg _) (isapropneg _)). 
assert (is3: isweq _ _ map1). apply isweqfibtototal. assumption. 
assert (is4: isweq _ _ map2). apply (isweqfpmap _ _ f  (fun y:Y => neg (paths _ y (f x))) is).
assert (h: forall x0':_, paths _ (map2 (map1 x0')) (maponcomplementsweq _ _ f is x x0')). intro.  simpl. destruct x0'. simpl. apply idpath.
apply (isweqhomot _ _ _ _ h (twooutof3c _ _ _ _ _ is3 is4)).
Defined.


Definition weqoncomplements (X Y:UU)(x:X)(w: weq X Y): weq (complement X x) (complement Y (pr21 _ _ w x)):= weqpair _ _ _ (isweqmaponcomplements X Y (pr21 _ _ w) (pr22 _ _ w) x).




Definition tocompltoii1x (X Y:UU)(x:X): coprod (complement X x) Y -> complement (coprod X Y) (ii1 _ _ x).
Proof. intros. destruct X0.  split with (ii1 _ _ (pr21 _ _ c)). 

assert (e: neg(paths _ (pr21 _ _ c) x)). apply (pr22 _ _ c). apply (negf _ _ (invmaponpathsincl _ _ (ii1 _ _) (isinclii1 X Y) _ _) e). 
split with (ii2 _ _ y). apply (negf _ _ (pathsinv0 _ _ _) (negpathsii1ii2 X Y x y)). Defined.



Definition fromcompltoii1x (X Y:UU)(x:X): complement (coprod X Y) (ii1 _ _ x) ->  coprod (complement X x) Y.
Proof. intros. destruct X0.  destruct t. 
assert (ne: neg (paths _ x1 x)). apply (negf _ _ (maponpaths _ _ (ii1 _ _) _ _) x0). apply (ii1 _ _ (complementpair _ _ x1 ne)). apply (ii2 _ _ y). Defined. 


Theorem isweqtocompltoii1x (X Y:UU)(x:X): isweq _ _ (tocompltoii1x X Y x).
Proof. intros. set (f:= tocompltoii1x X Y x). set (g:= fromcompltoii1x X Y x).
assert (egf:forall nexy:_ , paths _ (g (f nexy)) nexy). intro. destruct nexy. destruct c. simpl. 
assert (e: paths _ (negf (paths X t x) (paths (coprod X Y) (ii1 X Y t) (ii1 X Y x))
              (maponpaths X (coprod X Y) (ii1 X Y) t x)
              (negf (paths (coprod X Y) (ii1 X Y t) (ii1 X Y x))
                 (paths X t x)
                 (invmaponpathsincl X (coprod X Y) 
                    (ii1 X Y) (isinclii1 X Y) t x) x0)) x0). apply (isapropneg (paths X t x) _ _). 
apply (maponpaths _ _ (fun ee: neg(paths X t x) => ii1 _ _ (complementpair X x t ee)) _ _ e). 
apply idpath.
assert (efg: forall neii1x:_, paths _ (f (g neii1x)) neii1x). intro.  destruct neii1x. destruct t.  simpl. 
assert (e: paths _  (negf (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x)) 
           (paths X x1 x)
           (invmaponpathsincl X (coprod X Y) (ii1 X Y) (isinclii1 X Y) x1 x)
           (negf (paths X x1 x) (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x))
              (maponpaths X (coprod X Y) (ii1 X Y) x1 x) x0)) x0). apply (isapropneg (paths _ _ _)  _ _).
apply (maponpaths _ _ (fun ee: (neg (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x))) => (complementpair _ _ (ii1 X Y x1) ee)) _ _ e). 
simpl. 
assert (e: paths _ (negf (paths (coprod X Y) (ii2 X Y y) (ii1 X Y x))
           (paths (coprod X Y) (ii1 X Y x) (ii2 X Y y))
           (pathsinv0 (coprod X Y) (ii2 X Y y) (ii1 X Y x))
           (negpathsii1ii2 X Y x y)) x0). apply (isapropneg (paths _ _ _) _ _).
apply (maponpaths  _ _ (fun ee: (neg (paths (coprod X Y) (ii2 X Y y) (ii1 X Y x))) => (complementpair _ _ (ii2 X Y y) ee)) _ _ e). 
apply (gradth _ _ f g egf efg). Defined.






Definition tocompltoii2y (X Y:UU)(y:Y): coprod X (complement Y y) -> complement (coprod X Y) (ii2 _ _ y).
Proof. intros. destruct X0. 
split with (ii1 _ _ x). apply (negf _ _ (pathsinv0 _ _ _) (negpathsii2ii1 X Y x y)). 
split with (ii2 _ _ (pr21 _ _ c)). 
assert (e: neg(paths _ (pr21 _ _ c) y)). apply (pr22 _ _ c). apply (negf _ _ (invmaponpathsincl _ _ (ii2 _ _) (isinclii2 X Y) _ _) e). 
Defined.



Definition fromcompltoii2y (X Y:UU)(y:Y): complement (coprod X Y) (ii2 _ _ y) ->  coprod X (complement Y y).
Proof. intros. destruct X0.  destruct t. apply (ii1 _ _ x0). 
assert (ne: neg (paths _ y0 y)). apply (negf _ _ (maponpaths _ _ (ii2 _ _) _ _) x). apply (ii2 _ _ (complementpair _ _ y0 ne)). Defined. 


Theorem isweqtocompltoii2y (X Y:UU)(y:Y): isweq _ _ (tocompltoii2y X Y y).
Proof. intros. set (f:= tocompltoii2y X Y y). set (g:= fromcompltoii2y X Y y).
assert (egf:forall nexy:_ , paths _ (g (f nexy)) nexy). intro. destruct nexy. 
apply idpath.
destruct c. simpl. 
assert (e: paths _ (negf (paths _ t y) (paths (coprod X Y) (ii2 X Y t) (ii2 X Y y))
              (maponpaths _ (coprod X Y) (ii2 X Y) t y)
              (negf (paths (coprod X Y) (ii2 X Y t) (ii2 X Y y))
                 (paths _ t y)
                 (invmaponpathsincl _ (coprod X Y) 
                    (ii2 X Y) (isinclii2 X Y) t y) x)) x). apply (isapropneg (paths _ t y) _ _). 
apply (maponpaths _ _ (fun ee: neg(paths _ t y) => ii2 _ _ (complementpair _ y t ee)) _ _ e). 
assert (efg: forall neii2x:_, paths _ (f (g neii2x)) neii2x). intro.  destruct neii2x. destruct t.  simpl. 

assert (e: paths _ (negf (paths (coprod X Y) (ii1 X Y x0) (ii2 X Y y))
           (paths (coprod X Y) (ii2 X Y y) (ii1 X Y x0))
           (pathsinv0 (coprod X Y) (ii1 X Y x0) (ii2 X Y y))
           (negpathsii2ii1 X Y x0 y)) x). apply (isapropneg (paths _ _ _) _ _).
apply (maponpaths  _ _ (fun ee: (neg (paths (coprod X Y) (ii1 X Y x0) (ii2 X Y y))) => (complementpair _ _ (ii1 X Y x0) ee)) _ _ e). 
simpl.

assert (e: paths _  (negf (paths (coprod X Y) (ii2 X Y y0) (ii2 X Y y)) 
           _
           (invmaponpathsincl _ (coprod X Y) _ (isinclii2 X Y) y0 y)
           (negf (paths Y y0 y) (paths (coprod X Y) (ii2 X Y y0) (ii2 X Y y))
              (maponpaths Y (coprod X Y) (ii2 X Y) y0 y) x)) x). apply (isapropneg (paths _ _ _)  _ _).
apply (maponpaths _ _ (fun ee: (neg (paths (coprod X Y) (ii2 X Y y0) (ii2 X Y y))) => (complementpair _ _ (ii2 X Y y0) ee)) _ _ e). 
 
apply (gradth _ _ f g egf efg). Defined.












Definition tocompltodisjoint (X:UU): X -> complement (coprod X unit) (ii2 _ _ tt) := fun x:_ => complementpair _ _ (ii1 _ _ x) (negpathsii1ii2 _ _ x tt).

Definition fromcompltodisjoint (X:UU): complement (coprod X unit) (ii2 _ _ tt) -> X.
Proof. intros. destruct X0.  destruct t. assumption.  destruct u. apply (initmap _ (x (idpath _ (ii2 X _ tt)))). Defined.


Lemma isweqtocompltodisjoint (X:UU): isweq _ _ (tocompltodisjoint X).
Proof. intros. set (ff:= tocompltodisjoint X). set (gg:= fromcompltodisjoint X). 
assert (egf: forall x:X, paths _ (gg (ff x)) x).  intro.  apply idpath.
assert (efg: forall xx:_, paths _ (ff (gg xx)) xx). intro. destruct xx.  destruct t.   simpl.  unfold ff. unfold tocompltodisjoint. simpl. assert (ee: paths _  (negpathsii1ii2 X unit x0 tt) x).  apply (proofirrelevance _ (isapropneg _) _ _). induction ee. apply idpath. destruct u.  simpl. apply (initmap _ (x (idpath _ _))). apply (gradth _ _ ff gg egf efg).  Defined. 

Corollary isweqfromcompltodisjoint (X:UU): isweq _ _ (fromcompltodisjoint X).
Proof. intros. apply (isweqinvmap _ _ _ (isweqtocompltodisjoint X)). Defined. 















(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y 


Definition locsplit (X:UU)(Y:UU)(f:X -> Y):= forall y:Y, coprod (hfiber _ _ f y) (hfiber _ _ f y -> empty).

Definition dnegimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber _ _ f y)).
Definition dnegimageincl (X Y:UU)(f:X -> Y):= pr21 Y (fun y:Y => dneg(hfiber _ _ f y)).

Definition xtodnegimage (X:UU)(Y:UU)(f:X -> Y): X -> dnegimage _ _ f:= fun x:X => tpair _ _ (f x) ((todneg _) (hfiberpair _ _ f (f x) x (idpath _ (f x)))). 

Definition locsplitsec (X:UU)(Y:UU)(f:X->Y)(ls: locsplit _ _ f): dnegimage _ _ f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with 
ii1 z => pr21 _ _ z|
ii2 phi => initmap _ (psi phi)
end
end.


Definition locsplitsecissec  (X Y:UU)(f:X->Y)(ls: locsplit _ _ f)(u:dnegimage _ _ f): paths _ (xtodnegimage _ _ f (locsplitsec _ _ f ls u)) u.
Proof. intros.  set (p:= xtodnegimage _ _ f). set (s:= locsplitsec _ _ f ls).  
assert (paths _ (pr21 _ _ (p (s u))) (pr21 _ _ u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst.  simpl. apply (pr22 _ _ x0). induction (x y).  
assert (is: isofhlevelf (S O) _ _ (dnegimageincl _ _ f)). apply (isofhlevelfpr21 (S O) _ _ (fun y:Y => isapropdneg (hfiber _ _ f y))).  
assert (isw: isweq _ _ (maponpaths _ _ (dnegimageincl _ _ f) (p (s u)) u)). apply (isofhlevelfonpaths O _ _ _ _ _ is). 
apply (invmap _ _ _ isw X0). Defined.



Definition negimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber _ _ f y)).
Definition negimageincl (X Y:UU)(f:X -> Y):= pr21 Y (fun y:Y => neg(hfiber _ _ f y)).


Definition imsum (X:UU)(Y:UU)(f:X -> Y): coprod (dnegimage _ _ f) (negimage _ _ f) -> Y:= fun u:_ =>
match u with
ii1 z => pr21 _ _ z|
ii2 z => pr21 _ _ z
end.

*)
 




(** Some results on types with an isolated point. *)




Definition isisolated (X:UU)(x:X):= forall x':X, coprod (paths _ x' x) (paths _ x' x -> empty).


Lemma disjointl1 (X:UU): isisolated (coprod X unit) (ii2 _ _ tt).
Proof. intros.  unfold isisolated. intros.  destruct x'. apply (ii2 _ _ (negpathsii1ii2 _ _ x tt)).  destruct u.  apply (ii1 _ _ (idpath _ _ )). Defined.

Lemma isolatedtoisolatedii1 (X Y:UU)(x:X)(is:isisolated _ x): isisolated _ (ii1 X Y x).
Proof. intros.  intro.  destruct x'. destruct (is x0).  apply (ii1 _ _ (maponpaths _ _ (ii1 X Y) _ _ p)). apply (ii2 _ _ (negf _ _ (invmaponpathsincl _ _ (ii1 X Y) (isinclii1 X Y) _ _ ) e)). apply (ii2 _ _ (negpathsii2ii1 _ _ x y)). Defined. 


Lemma isolatedtoisolatedii2 (X Y:UU)(y:Y)(is:isisolated _ y): isisolated _ (ii2 X Y y).
Proof. intros.  intro.  destruct x'. apply (ii2 _ _ (negpathsii1ii2 _ _ x y)). destruct (is y0).  apply (ii1 _ _ (maponpaths _ _ (ii2 X Y) _ _ p)). apply (ii2 _ _ (negf _ _ (invmaponpathsincl _ _ (ii2 X Y) (isinclii2 X Y) _ _ ) e)).  Defined. 


Lemma isolatedifisolatedii1 (X Y:UU)(x:X)(is: isisolated _ (ii1 X Y x)): isisolated _ x.
Proof. intros. intro.  destruct (is (ii1 _ _ x')).  apply (ii1 _ _ (invmaponpathsincl _ _ _ (isinclii1 _ _) _ _ p)). apply (ii2 _ _ (negf _ _ (maponpaths _ _ (ii1 _ _) _ _) e)). Defined. 



Lemma isolatedifisolatedii2 (X Y:UU)(y:Y)(is: isisolated _ (ii2 X Y y)): isisolated _ y.
Proof. intros. intro.    destruct (is (ii2 _ _ x')).  apply (ii1 _ _ (invmaponpathsincl _ _ _ (isinclii2 _ _) _ _ p)). apply (ii2 _ _ (negf _ _ (maponpaths _ _ (ii2 _ _) _ _) e)).  Defined. 




Definition recomplinv (X:UU)(x:X)(is: isisolated X x): X -> coprod (complement X x) unit:=
fun x':X => match (is x') with
ii1 e => ii2 _ _ tt|
ii2 phi => ii1 _ _ (complementpair _ _ x' phi)
end.



Theorem isweqrecompl (X:UU)(x:X)(is:isisolated X x): isweq _ _ (recompl X x).
Proof. intros. set (f:= recompl X x). set (g:= recomplinv X x is). unfold recomplinv in g. simpl in g. 

assert (efg: forall x':X, paths _ (f (g x')) x'). intro.   induction (is x').   induction x0. unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x').  simpl. apply idpath. induction (y (idpath _ x')).  unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x').  induction (y x0). simpl. apply idpath. 


assert (egf: forall u: coprod  (complement X x) unit, paths _ (g (f u)) u). unfold isisolated in is. intro. destruct (is (f u)). destruct u.    simpl. destruct c. simpl in p. destruct (x0 p). destruct u.   
assert (e1: paths _  (g (f (ii2 (complement X x) unit tt))) (g x)). apply (maponpaths _ _ g _ _ p). 
assert (e2: paths _ (g x) (ii2 (complement X x) unit tt)). unfold g.  destruct (is x).   apply idpath.  destruct (e (idpath _ x)). apply (pathscomp0 _ _ _ _ e1 e2). destruct u.  simpl. destruct c.  simpl. unfold isisolated in is.  unfold g.  destruct (is t). destruct (x0 p). simpl in g. 
 unfold f. unfold recompl. simpl in e. 
assert (ee: paths _ e0 x0). apply (proofirrelevance _ (isapropneg (paths _ t x))). induction ee.  apply idpath. 
unfold f. unfold g. simpl. induction u. induction (is x).  apply idpath. induction (y (idpath _ x)).
apply (gradth _ _ f g egf efg). Defined.


Lemma isolatedtoisolated (X:UU)(Y:UU)(f:X -> Y)(is1:isweq _ _ f)(x:X)(is2: isisolated _ x): isisolated _ (f x).
Proof.  intros. unfold isisolated. intro. rename x' into y.  set (g:=invmap _ _ f is1). set (x':= g y). induction (is2 x').  apply (ii1 _ _ (pathsinv0 _ _ _ (pathsweq1' _ _ f is1 x y (pathsinv0 _ _ _ x0)))). 
assert (phi: paths _ y (f x)  -> empty). 
assert (psi: (paths _ (g y) x -> empty) -> (paths _ y (f x) -> empty)). intro. intro.  apply (X0  (pathsinv0 _ _ _ (pathsweq1 _ _ f is1 x y (pathsinv0 _ _ _ X1)))). apply (psi y0). apply (ii2 _ _ phi). Defined.


















(** * Experiments with different version of "inhabited" construction. *)


Definition isinhudneg (X:UU):UU := dneg X.
Definition isinhudnegpr (X:UU): X -> isinhudneg X := todneg X.
Definition isinhudnegfunct (X Y:UU)(f:X -> Y): isinhudneg X -> isinhudneg Y := dnegf _ _ f.
Definition isinhudneguniv (X: UU)(P:UU)(is:isweq _ _ (todneg P)): (X -> P) -> ((isinhudneg X) -> P) := fun xp:_ => fun inx0:_ => (invmap _ _ _ is (dnegf _ _ xp inx0)).
Definition isinhudnegand (X Y:UU)(inx0: isinhudneg X)(iny0: isinhudneg Y) : isinhudneg (dirprod X Y) := dneganddnegimpldneg _ _ inx0 iny0.




Definition isinhu (X:UU) := forall P:UU, forall is: isaprop P, ((X->P)->P). (* Note that isinhu types to UU+1 . *)
Definition isinhupr (X:UU): X -> isinhu X := fun x:X => fun P:UU => fun is:_ => adjev X P x.
Definition isinhufunct (X Y:UU)(f:X -> Y) : isinhu X -> isinhu Y := fun inx1: isinhu X => fun P:_ => fun is:_ => fun yp: Y -> P => (inx1 P is (fun x: X => yp (f x))).
Definition isinhuuniv (X:UU)(P:UU)(is:isaprop P): (X -> P) -> ((isinhu X) -> P) := fun xp:_ => fun inx1:_ => inx1 P is xp.
Definition isinhuand (X Y:UU)(inx1: isinhu X)(iny1: isinhu Y) : isinhu (dirprod X Y):= fun P:_ => fun is:_ => ddualand X Y P (inx1 P is) (iny1 P is).
Definition isinhufunct2 (X Y Z:UU): (X -> Y -> Z) -> (isinhu X -> isinhu Y -> isinhu Z).
Proof. intros. apply (isinhufunct _ _ (fun xy: dirprod X Y => X0 (pr21 _ _ xy) (pr22 _ _ xy)) (isinhuand _ _ X1 X2)).  Defined. 


Definition isinhuimplisinhudneg (X:UU)(inx1: isinhu X): isinhudneg X := inx1 empty isapropempty.















(** * Finite sets. *)



(** ** Standard finite sets. *)



Fixpoint stn (n:nat):UU:= match n with
O => empty|
S m => coprod (stn m) unit
end.

 

Lemma isisolatedinstn (n:nat): forall x: stn n, isisolated _ x.
Proof. intro.   induction n. intro. apply (initmap _ x). intro.  simpl in x.  destruct x. apply (isolatedtoisolatedii1 _ _ s (IHn s)). destruct u. 
apply disjointl1.  Defined. 



Corollary isdeceqstn (n:nat): isdeceq (stn n).
Proof. intro.  unfold isdeceq. apply (isisolatedinstn n). Defined. 


Lemma stnsnegl1 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ X lp). Defined.

Lemma stnsnegl2 (n:nat): neg (weq (stn O) (stn (S n))).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ (weqinv _ _ X) lp). Defined.


Lemma stnsposl0 (n:nat): weq (stn n) (complement (stn (S n)) (ii2 _ _ tt)).
Proof. intros. split with (tocompltodisjoint (stn n)). apply isweqtocompltodisjoint. Defined.

Lemma stnsposl1 (n:nat)(x: stn (S n)): weq (stn n) (complement (stn (S n)) x).
Proof. intro. induction n. intros. simpl in x.  destruct x.  apply (initmap _ e). simpl. destruct u. apply (stnsposl0 O). intro. simpl in x. destruct x. set  (g:=tocompltoii1x _ unit c).  set (f:= coprodf _ _ _ _ (pr21 _ _ (IHn c)) (fun t:unit => t)).  split with (fun x:_ => g (f x)). 
assert (is1:isweq _ _ f). apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ (IHn c)) (idisweq unit)). 
assert (is2: isweq _ _ g). apply (isweqtocompltoii1x _ unit c). 
apply (twooutof3c _ _ _ f g is1 is2). 
destruct u. split with (tocompltodisjoint _). apply (isweqtocompltodisjoint _).  Defined.






Lemma stnsposl2 (n n':nat): weq (stn (S n)) (stn (S n')) -> weq (stn n) (stn n').
Proof. intros. destruct X. rename t into ff. rename x into is.    simpl in ff. set (int1:= complement (stn (S n')) (ff (ii2 _ _ tt))).
set (f1:= tocompltodisjoint (stn n)).  
set (f2:= maponcomplementsweq _ _ ff is (ii2 _ _ tt)).
set (f3:= invmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
assert (is1: isweq _ _ f1). apply isweqtocompltodisjoint. 
assert (is2: isweq _ _ f2). apply isweqmaponcomplements.
assert (is3: isweq _ _ f3). apply (isweqinvmap _ _ _ (pr22 _ _ (stnsposl1 n' (ff (ii2 _ _ tt))))).
set (gg:= fun xx:_ => (f3 (f2 (f1 xx)))). split with gg.
apply (twooutof3c _ _ _ _ _ (twooutof3c _ _ _ _ _ is1 is2) is3). Defined.



Theorem stnsweqtoeq (n n':nat): (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intro. induction n. intro. induction n'.  intros. apply idpath. intro. apply (initmap _ (stnsnegl2  n' X)).  
 intro. induction n'. intros. set (int:= isdeceqnat O (S n)).  destruct int.  assumption. apply (initmap _ (stnsnegl1 n X)).  intro. 
set (e:= IHn n' (stnsposl2 n n' X)). apply (maponpaths _ _ S _ _ e). Defined. 

Corollary stnsdnegweqtoeq (n n':nat): dneg (weq (stn n) (stn n')) -> paths _ n n'.
Proof. intros. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf _ _ (stnsweqtoeq n n') X)). Defined. 






(** ** Sets with fixed number of elements. *)



Definition nelstruct (n:nat)(X:UU):= weq (stn n) X. 
Definition isofnel (n:nat)(X:UU) := isinhu (weq (stn n) X). 

Definition isofnelstn (n:nat): isofnel n (stn n) := isinhupr _ (idweq (stn n)).

Lemma isofnelimpl (n:nat)(X:UU)(isx: isofnel n X)(P: UU)(isp: isaprop P): ((weq (stn n) X) -> P) -> (isofnel n X -> P).
Proof. intros.  apply isinhuuniv with (weq (stn n) X). assumption. assumption. assumption.  Defined. 



Lemma isof0ela (X:UU): isofnel O X -> neg X.
Proof. intros. intro. apply (isofnelimpl O X X0 empty  isapropempty). intro.  apply (invmap _ _ _ (pr22 _ _ X2) X1). assumption.  Defined. 


Lemma isof0elb (X:UU): neg X -> isofnel O X.
Proof. intros. apply (isinhupr _ (weqinv _ _ (weqpair _ _ _ (isweqtoempty _ X0)))). Defined. 


Corollary isof0elempty: isofnel O empty.
Proof. apply (isof0elb empty (fun x:_ => x)). Defined. 

Lemma isof1ela (X:UU): isofnel (S O) X -> iscontr X.
Proof. intros.  apply (isofnelimpl (S O) X X0 (iscontr X)  (isapropiscontr X)).  set (w2:= (weqinv _ _ (weqfromcoprodwithempty unit))). intro.  set (w3:= weqcomp _ _ _ w2 X1). apply (iscontrifweqtounit _ (weqinv _ _ w3)). assumption. Defined.  

Lemma isof1elb (X:UU): (iscontr X) -> isofnel (S O) X.
Proof. intros. set (w1:= weqpair _ _ _ (isweqcontrtounit _ X0)). set (w2:= weqfromcoprodwithempty unit).  set (w:= weqcomp _ _ _ w2 (weqinv _ _ w1)). apply (isinhupr _ w). Defined. 


Lemma isof1elunit: isofnel (S O) unit.
Proof. apply (isinhupr _ (weqfromcoprodwithempty unit)). Defined. 


Lemma isofsnel (n:nat)(X:UU): isofnel n X -> isofnel (S n) (coprod X unit).
Proof. intros. 
assert (f: weq (stn n) X -> weq (stn (S n)) (coprod X unit)).  intro.  split with (coprodf _ _ _ _ (pr21 _ _ X1) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X1) (idisweq unit)). apply (isinhufunct _ _ f X0). Defined.


Lemma isofnelweqf (n:nat)(X Y:UU)(f:X -> Y)(is: isweq _ _ f): isofnel n X -> isofnel n Y.
Proof. intros.  set (ff:= fun u:weq (stn n) X => weqcomp _ _ _ u (weqpair _ _ f is)). apply (isinhufunct _ _ ff X0). Defined.


Lemma isof2elbool : isofnel (S (S O)) bool.
Proof. apply (isofnelweqf _ _ _ _ (pr22 _ _ boolascoprod) (isofsnel (S O) unit isof1elunit)). Defined. 



(** ** Finite subsets of nat. *)

Fixpoint leb (n m : nat) : bool :=
match n,m with
 | S n , S m => leb n m
 | 0, _ => true
 | _, _ => false
end.


Lemma isreflleb (n:nat): paths _ (leb n n) true.
Proof. intros. induction n. apply idpath.  simpl. assumption.  Defined. 

Lemma islebnsn (n:nat): paths _ (leb n (S n)) true.
Proof. intro. induction n.  apply idpath. simpl.  assumption.  Defined. 

Lemma neglebsnn (n:nat): neg (paths _ (leb (S n) n) true).
Proof. intro. induction n.  simpl.  intro. apply (nopathsfalsetotrue X). assumption.  Defined.


Lemma istransleb (k m n : nat): paths _ (leb k m) true -> paths _ (leb m n) true -> paths _ (leb k n) true.
Proof. intro. induction k.  intros.  simpl. apply idpath. intro. destruct m.  intros.   simpl in X.   apply (initmap _ (nopathsfalsetotrue X)). intro. destruct n.  intros.  apply (initmap _ (nopathsfalsetotrue X0)). simpl. apply (IHk m n).  Defined. 


Lemma is0leb0 (n:nat) : paths _ (leb n 0) true -> paths _ n 0.
Proof.  intro. destruct n. intro.   apply idpath.  intro. apply (initmap _ (nopathsfalsetotrue X)). Defined. 

Lemma lebsnchoice0 (x n:nat): paths _ (leb x (S n)) true -> (neg (paths _ x (S n))) -> paths _ (leb x n) true.
Proof. intro. induction x.  intros. apply idpath.  intro. destruct n.  intros.  simpl in X.  destruct x.  apply (initmap _ (X0 (idpath _ _))). simpl in X.  apply (initmap _ (nopathsfalsetotrue X)). intros. simpl in X.  set (a:= IHx n X (negf _ _ (maponpaths _ _ S _ _) X0)).  assumption.  Defined. 

Lemma lebsnchoice (x n:nat) : paths _ (leb x (S n)) true -> coprod (paths _ (leb x n) true) (paths _ x (S n)).
Proof. intros. set (s:= isdeceqnat (S n) x).  destruct s.  apply (ii2 _ _ p).
apply (ii1 _ _ (lebsnchoice0 x n X e)).  Defined. 


Definition initinterval (n:nat) := total2 nat (fun x:nat => paths _ (leb x n) true).
Definition initintervalpair (n:nat):= tpair  nat (fun x:nat => paths _ (leb x n) true).
Definition initintervaltonat (n:nat): initinterval n -> nat := pr21 _ _. 

Lemma isinclinitintervaltonat (n:nat) : isincl _ _ (initintervaltonat n).
Proof. intro.  apply isofhlevelfpr21. intro. intro.  intro. apply (isasetbool (leb x n) true). Defined. 

Definition initintervalsincl (m n:nat)(isle: paths _ (leb m n) true) : initinterval m -> initinterval n.
Proof. intros. destruct X.  split with t.  simpl. apply (istransleb t m n x isle).  Defined. 
 

Lemma iscontrinitinterval0 : iscontr (initinterval O).
Proof. split with (initintervalpair O O (isreflleb O)).  intro. destruct t.  assert (e: paths _ O t). apply (pathsinv0 _ _ _ (is0leb0 t x)).  destruct e. simpl.  apply (invmaponpathsincl _ _ _ (isinclinitintervaltonat O) (tpair nat (fun x0 : nat => paths bool (leb x0 O) true) O x)
     (initintervalpair O O (idpath bool true)) (idpath _ O)). Defined. 


Definition toinitintervalsn (n:nat):  (coprod (initinterval n) unit) -> (initinterval (S n)) := sumofmaps ( initintervalsincl n (S n) (islebnsn n)) (fun t:unit => initintervalpair (S n) (S n) (isreflleb (S n))).

Definition frominitintervalsn (n:nat): initinterval (S n) -> coprod (initinterval n) unit.
Proof. intros.   destruct X.  destruct (isdeceqnat (S n) t).  apply (ii2 _ _ tt).  apply (ii1 _ _ (initintervalpair n t (lebsnchoice0 t n x e))).   Defined. 


Definition weqtoinitintervalsn  (n:nat) : weq  (coprod (initinterval n) unit) (initinterval (S n)).
Proof. intro. set (f:= toinitintervalsn n). set (g:= frominitintervalsn n). split with f. 
set (u:= coprodf _ _ _ _ (initintervaltonat n) (fun t:unit => t)).   assert (is: isincl _ _ u). apply (isofhlevelfcoprodf (S O) _ _ _ _ _ _ (isinclinitintervaltonat n) (isofhlevelfweq (S O) _ _ _ (idisweq unit))).  
assert (egf: forall x:_, paths _ (g (f x)) x).  intro. 
assert (egf0: paths _ (u (g (f x))) (u x)).  destruct x. simpl. destruct i. destruct t.   simpl.  apply idpath. simpl. destruct (isdeceqnat n t).    simpl. induction p. apply (initmap _ (neglebsnn t x)).  simpl.  apply idpath.  destruct u0. destruct n.  apply idpath. simpl.  destruct (isdeceqnat n n). apply idpath.  apply (initmap _ (e (idpath _ _))). apply (invmaponpathsincl _ _ _ is _ _ egf0). 
assert (efg: forall x:_, paths _ (f (g x)) x). intro. 
assert (efg0: paths _ (initintervaltonat (S n) (f (g x))) (initintervaltonat (S n) x)).  destruct x. simpl.  destruct t. apply idpath. destruct (isdeceqnat n t).  simpl. apply (pathsinv0 _ _ _ (maponpaths _ _ S _ _ p)).  simpl.  apply idpath.  apply  (invmaponpathsincl _ _ _ (isinclinitintervaltonat _)  _ _ efg0). 
apply (gradth _ _ _ _ egf efg). Defined.  



Theorem weqstntoinitinterval (n:nat): weq (stn (S n)) (initinterval n).
Proof. intro. induction n. set (w1:= weqfromcoprodwithempty unit). set (w2:= weqinv _ _ (weqpair _ _ _ (isweqcontrtounit _ (iscontrinitinterval0)))).     apply (weqcomp _ _ _ w1 w2).  apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ IHn (idweq unit)) (weqtoinitintervalsn n)). Defined. 





(** ** General finite sets. *)



Definition finitestruct (X:UU):= total2 nat (fun n:nat => weq (stn n) X).
Definition finitestructpair (X:UU) := tpair nat (fun n:nat => weq (stn n) X).
Definition isfinite (X:UU):= isinhu (finitestruct X).
Definition isfiniteimpl (X:UU)(P:UU)(isp: isaprop P): (forall n:nat, forall w: weq (stn n) X, P) -> isfinite X -> P.
Proof. intros. set (f0:= fun xx:(total2 nat (fun n:_ => weq (stn n) X)) => (X0 (pr21 _ _ xx) (pr22 _ _ xx))).  apply (isinhuuniv (total2 nat (fun n:nat => weq (stn n) X)) P isp f0 X1). Defined. 


Definition isfiniteifofnel (n:nat)(X:UU): isofnel n X -> isfinite X.
Proof. intros.  apply (isinhufunct _ _ (fun w:weq (stn n) X => finitestructpair _ n w) X0).  Defined.



Definition isofnel0 (n:nat)(X:UU):= dneg (weq (stn n) X).
Definition isfinite0 (X:UU):= total2 nat (fun n:_ => isofnel0 n X).



Lemma isapropisfinite0 (X:UU): isaprop (isfinite0 X).
Proof. intros. assert (is1: (isfinite0 X) -> (iscontr (isfinite0 X))).  intro. unfold iscontr. split with X0.  intro. destruct X0.  destruct t.
assert (c1: coprod (paths _ t t0) (neg (paths _ t t0))). apply isdeceqnat. destruct c1.  apply (invmaponpathsincl (isfinite0 X) nat (pr21 _ _) (isofhlevelfpr21 (S O) _ _  (fun n:nat => isapropdneg (weq (stn n) X))) (tpair nat (fun n : nat => isofnel0 n X) t x0) (tpair nat (fun n : nat => isofnel0 n X) t0 x) p).  
assert (is1: dneg (dirprod (weq (stn t0) X) (weq (stn t) X))). apply (dneganddnegimpldneg _ _ x x0). 
assert (is2: dneg (weq (stn t0) (stn t))). apply (dnegf _ _ (fun fg: dirprod (weq (stn t0) X) (weq (stn t) X) => weqcomp _ _ _ (pr21 _ _ fg) (weqinv _ _ (pr22 _ _ fg))) is1).   apply (initmap _ (dnegf _ _ (fun ee:_ => pathsinv0 _ _ _ (stnsweqtoeq t0 t ee)) is2 n)). apply (iscontraprop1inv _ is1). Defined. 


Lemma isfiniteimplisfinite0 (X:UU): isfinite X -> isfinite0 X.
Proof. intros. 
assert (nw: forall n:nat, forall w: weq (stn n) X, isfinite0 X). intros. split with n. apply (todneg _  w).  
apply (isfiniteimpl X (isfinite0 X) (isapropisfinite0 X) nw X0). Defined.


Definition card (X:UU)(is: isfinite X): nat:= pr21 _ _ (isfiniteimplisfinite0 X is).

Definition preweq (X:UU)(is: isfinite X): isofnel (card X is) X.
Proof. intros.  set (c:= card X is). set (dnw:= pr22 _ _ (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr21 nat (fun n : nat => isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw. 

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intros. destruct X0.  destruct t. 
assert (dw: dneg (weq (stn t) (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr21 _ _ ab) (weqinv _ _ (pr22 _ _ ab))).  apply (dnegf _ _ ff (isinhudnegand _ _ (todneg _ x0) x)). 
assert (e:paths _ t c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel. 
apply (isinhufunct _ _ f (isinhuand (finitestruct X) _ is (isinhupr _ dnw))). Defined. 





(* To be completed 


Lemma finiteprops (X:UU)(is1: isaprop X)(is2: isfinite X): coprod X  (neg X).
Proof. intros. 
assert (is: isaprop (coprod X (neg X))). apply isapropisdec. assumption. 
assert (f: (total2 nat (fun n:nat => weq (stn n) X)) -> coprod X (neg X)).  intros. destruct X0.  


*)


Definition finitestructstn (n:nat):= finitestructpair _ n (idweq _).
Definition isfinitestn (n:nat): isfinite (stn n) := isinhupr _ (finitestructstn n). 

Definition finitestructempty := finitestructpair _ O (idweq _).
Definition isfiniteempty : isfinite empty := isinhupr _ finitestructempty.

Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).
Definition isfiniteunit : isfinite unit := isinhupr _ finitestructunit. 

Definition finitestructbool := finitestructpair _ (S (S O)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (weqfromcoprodwithempty unit) (idweq unit)) boolascoprod).
Definition isfinitebool : isfinite bool  := isinhupr _ finitestructbool.

Definition finitestructinitinterval (n:nat) := finitestructpair _ (S n) (weqstntoinitinterval n).
Definition isfiniteinitinterval (n:nat):= isinhupr _ (finitestructinitinterval n).


Theorem finitestructweqf (X Y:UU)(f:X -> Y)(is:isweq _ _ f) : finitestruct X -> finitestruct Y.
Proof. intros.   destruct X0. split with t. apply (weqcomp _ _ _ x (weqpair _ _ f is)). Defined. 

Theorem isfiniteweqf (X Y:UU)(f:X -> Y)(is:isweq _ _ f) : isfinite X -> isfinite Y.
Proof. intros. apply (isinhufunct _ _ (finitestructweqf _ _ f is) X0). Defined. 


(* to be completed 

Theorem cardweqf (X Y:UU)(f: X -> Y)(isw:isweq _ _ f)(isx: isfinite X): paths _ (card _ isx) (card _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *) 


Lemma finitestructcoprodwithunit  (X:UU): finitestruct X -> finitestruct (coprod X unit).
Proof. intros.  destruct X0. split with (S t).  
assert (f: weq (stn t) X -> weq (stn (S t)) (coprod X unit)).  intro.  split with (coprodf _ _ _ _ (pr21 _ _ X0) (fun t:_=> t)).  apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ X0) (idisweq unit)). apply (f x). Defined. 

Lemma isfinitecoprodwithunit (X:UU): isfinite X -> isfinite (coprod X unit).
Proof. intros. apply (isinhufunct _ _ (finitestructcoprodwithunit _) X0). Defined. 


Theorem finitestructcoprod (X Y:UU) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (coprod X Y).
Proof. intros. destruct isy. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx.  split with t. apply (weqcomp _ _ _ (weqcomp _ _ _ (weqinv _ _ (weqfromcoprodwithempty (stn t))) (weqcoprodcomm empty (stn t))) (weqcoprodf _ _ _ _ x0 x)).  

intros.  set (st0t:= IHt (stn t) (coprod X unit) (finitestructcoprodwithunit _ isx) (idweq _ )). 
assert (w: weq (coprod (coprod X unit) (stn t)) (coprod X Y)). apply (weqcomp _ _ _ (weqcoprodasstor X unit (stn t)) (weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq X) (weqcoprodcomm unit (stn t))) (weqcoprodf _ _ _ _ (idweq X) x))). 
apply (finitestructweqf _ _ _ (pr22 _ _ w) st0t). Defined.

Theorem isfinitecoprod (X Y:UU) (isx: isfinite X)(isy: isfinite Y): isfinite (coprod X Y).
Proof. intros. apply (isinhufunct2 _ _ _ (finitestructcoprod X Y) isx isy). Defined.



Theorem finitestructdirprod (X Y:UU) (isx: finitestruct X)(isy: finitestruct Y): finitestruct (dirprod X Y).
Proof. intros. destruct isy. generalize Y X isx x.  clear isx x X Y. induction t.  intros. destruct isx. split with O.  set (f:= fun xy:dirprod X Y => pr21 _ _ (weqinv _ _ x) (pr22 _ _ xy)). set (is:= isweqtoempty _ f). apply (weqinv _ _ (weqpair _ _ _ is)). 

intros. set (w:= weqcomp _ _ _ (weqcoprodf _ _ _ _ (idweq (dirprod X (stn t))) (weqtodirprodwithunit X)) (weqcomp _ _ _ (weqrdistrtoprod X (stn t) unit) (weqdirprodf _ _ _ _ (idweq X) x))). apply (finitestructweqf _ _ _ (pr22 _ _ w) (finitestructcoprod _ _ (IHt (stn t) X isx (idweq _)) isx)). Defined. 

Theorem isfinitedirprod (X Y:UU)(isx: isfinite X)(isy: isfinite Y): isfinite (dirprod X Y).
Proof. intros. apply  (isinhufunct2 _ _ _ (finitestructdirprod X Y) isx isy). Defined.



Theorem finitestructcomplement (X:UU)(x:X)(is:finitestruct X): finitestruct (complement X x).
Proof. intros.  destruct is.   destruct t.   apply (initmap _ (invmap _ _ _ (pr22 _ _ x0) x)).

set (w:= weqcomp _ _ _ (stnsposl1 t _ ) (weqinv _ _ (weqoncomplements _ _ x (weqinv _ _ x0)))). 
split with t. assumption.  Defined.  


Theorem  isfinitecomplement (X:UU)(x:X)(is:isfinite X): isfinite (complement X x).
Proof. intros. apply (isinhufunct _ _ (finitestructcomplement X x) is). Defined. 


Theorem finitestructfromcomplement (X:UU)(x:X)(is:isisolated _ x): finitestruct (complement X x) -> finitestruct X.
Proof. intros. destruct X0.  split with (S t). 
assert (w1: weq (coprod (complement X x) unit) X). apply (weqpair _ _ _ (isweqrecompl X x is)). apply (weqcomp _ _ _ (weqcoprodf _ _ _ _ x0 (idweq _)) w1). Defined.


Theorem isfiniteifcomplement (X:UU)(x:X)(is: isisolated _ x): isfinite (complement X x) -> isfinite X.
Proof. intros. apply (isinhufunct _ _ (finitestructfromcomplement X x is) X0). Defined. 


Theorem finitestructsummand (X Y:UU)(is: finitestruct (coprod X Y)): finitestruct X.
Proof. intros. destruct is.  generalize X Y x.  clear X Y x. induction t.  intros.  split with O. assert (w: weq X empty). apply (weqpair _ _ _ (isweqtoempty _ (fun x0:X => invmap _ _ _ (pr22 _ _ x) (ii1 _ _ x0)))). apply (weqinv _ _ w).  

intros. set (xy:= pr21 _ _ x (ii2 _ _ tt)). 
assert (is: isisolated _ xy). apply (isolatedtoisolated _ _ _ (pr22 _ _ x) (ii2 _ _ tt) (isisolatedinstn (S t) (ii2 _ _ tt))). 
assert (w1: weq (stn t) (complement _ xy)).  apply (weqcomp _ _ _ (stnsposl0 t) (weqoncomplements _ _ (ii2 _ _ tt) x)). destruct xy. 
assert (w2: weq (complement (coprod X Y) (ii1 X Y x0)) (coprod (complement X x0) Y)). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii1x _ _ x0))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)).

assert (isx: isisolated _ x0). apply (isolatedifisolatedii1 _ _ _ is). apply (finitestructfromcomplement _ _ isx is1). 

assert (w2: weq (complement (coprod X Y) (ii2 X Y y)) (coprod X (complement Y y))). apply (weqinv _ _ (weqpair _ _ _ (isweqtocompltoii2y _ _ y))). set (is1:=IHt _ _ (weqcomp _ _ _ w1 w2)). assumption.  Defined. 

Theorem isfinitesummand (X Y:UU)(is:isfinite (coprod X Y)): isfinite X.
Proof. intros.  apply (isinhufunct _ _ (finitestructsummand X Y) is). Defined. 


Theorem finitestructsubset (X:UU)(f:X -> bool): finitestruct X -> finitestruct (hfiber _ _ f true).
Proof. intros. 
assert (w: weq (coprod (hfiber _ _ f true) (hfiber _ _ f false)) X). apply weqsubsetsplit. apply (finitestructsummand _ _ (finitestructweqf _ _ _ (pr22 _ _ (weqinv _ _ w)) X0)).   Defined. 


Theorem isfinitesubset  (X:UU)(f:X -> bool): isfinite X -> isfinite (hfiber _ _ f true).
Proof. intros. apply  (isinhufunct _ _ (finitestructsubset X f) X0). Defined. 


















(** ** Test computations. *)



(*Eval compute in card _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O))))).*)

Eval compute in card _ (isfiniteempty).

Eval compute in card _ (isfiniteunit).

Eval lazy in card _  (isfinitebool).




(*Eval lazy in   (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).*)
 



Eval lazy in card _ (isfinitecomplement _ true isfinitebool).

Eval compute in card _ (isfinitedirprod _ _ isfinitebool isfinitebool).

Eval compute in card _ (isfinitedirprod _ _ isfinitebool (isfinitedirprod _ _ isfinitebool isfinitebool)).

Eval compute in card _ (isfinitecoprod _ _ (isfinitebool) (isfinitecomplement _ (ii1 _ _ (ii2 _ _ tt)) (isfinitestn (S (S (S O)))))).

Eval lazy in card _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).

(*Eval compute in  card _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool))).*)

(*Eval compute in card _ (isfinitecomplement _ (dirprodpair _ _ tt tt) (isfinitedirprod _ _ isfiniteunit isfiniteunit)).*)


(*Definition finitestructunit: finitestruct unit := finitestructpair _ (S O) (weqfromcoprodwithempty unit).*)

Eval lazy in (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).
 


Eval lazy in card _ (isfinitecomplement _ (dirprodpair _ _ true (dirprodpair _ _ true false)) (isfinitedirprod _ _ (isfinitebool) (isfinitedirprod _ _ (isfinitebool) (isfinitebool)))).









(*

Eval compute in (pr21 _ _ (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O)))))).


Print empty_rect. 

Lemma isof1elfrom0el (X Y:UU): isofnel O X -> isofnel (S O) (X -> Y).
Proof. intros. unfold isofnel. intro.   simpl. 

Theorem isfinitefunctions (X Y:UU)(isx: isfinite X)(isy: isfinite Y): isfinite (X -> Y).
Proof. intros. destruct isx.  generalize Y isy X x. clear isy Y x X.  induction t.  intros. split with (S O). 



*)


































(* End of the file univ.v *)


