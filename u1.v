
  
Definition UU:=Type.
Inductive empty:UU := .
Inductive unit:UU := tt:unit.
Inductive bool:UU := true:bool | false:bool.
Inductive nat:UU := O:nat | S: nat -> nat.





Inductive paths (T:UU)(t:T): T -> UU := idpath: paths T t t.

(** Operations on paths **)

Definition pathscomp0 (T:UU) (a:T)(b:T) (c:T)(e1: paths _ a b)(e2:paths _ b c): paths _ a c.
Proof. intros. induction e1.  assumption. Defined.

Definition pathscomp0rid  (T:UU) (a:T)(b:T)(e1: paths _ a b): paths _ (pathscomp0 _ _ b b e1 (idpath _ b)) e1. 
Proof. intros.  induction e1. simpl. apply idpath.  Defined. 

Definition pathsinv0 (T:UU) (a:T) (b:T)(e: paths _ a b): paths _ b a.
Proof. intros. induction e.  apply idpath. Defined. 

Definition pathsinv0l1 (X:UU)(a:X)(b:X)(e: paths _ a b): paths _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ e) e) (idpath _ _).
Proof. intros. induction e. simpl. apply idpath. Defined. 


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
Proof. intros. unfold maponpaths. simpl. apply idpath. Qed. 


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


(* The following four statements show that maponpaths defined by a function f which is homotopic to the identity is "surjective". It is later used to show that the maponpaths defined by a function which is a weak equivalence is itself a weak equivalence. *) 


Definition maponpathshomidinv (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X): paths _ (f x) (f x') -> paths _ x x' := (fun e: paths _ (f x) (f x') => pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))).


Lemma maponpathshomid1 (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ x x'): paths _ (maponpaths _ _ f _ _ e) (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ e (pathsinv0 _ _ _ (h x')))).
Proof. intros. induction e. change (pathscomp0 X x x (f x) (idpath X x) (pathsinv0 X (f x) x (h x))) with (pathsinv0 X (f x) x (h x)). assert (ee: paths _  (maponpaths X X f x x (idpath X x)) (idpath _ (f x))). apply idtoid1. 
assert (eee: paths _ (idpath _ (f x)) (pathscomp0 X (f x) x (f x) (h x)  (pathsinv0 X (f x) x (h x)))). apply (pathsinv0 _ _ _ (pathsinv0r1 _ _ _ (h x))). apply (pathscomp0 _ _ _ _ ee eee). Defined. 


Lemma maponpathshomid12 (X:UU)(x:X)(x':X)(fx:X)(fx':X)(e:paths _ fx fx')(hx:paths _ fx x)(hx':paths _ fx' x'): paths _   (pathscomp0 _ _ _ _ (hx) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (hx)) (pathscomp0 _ _ _ _ e (hx'))) (pathsinv0 _ _ _ (hx')))) e.
Proof. intros. induction hx. induction hx'. induction e.  simpl. apply idpath. Defined. 


Lemma maponpathshomid2 (X:UU)(f:X->X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ (f x) (f x')): paths _ (maponpaths _ _ f _ _ (maponpathshomidinv _ f h _ _ e)) e.
Proof.  intros. assert (ee: paths _ (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))) (pathsinv0 _ _ _ (h x')))) e). apply (maponpathshomid12 _ _ _ (f x) (f x') e (h x) (h x')). assert (eee: paths _ (maponpaths _ _ f _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x')))) (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ (h x)) (pathscomp0 _ _ _ _ e (h x'))) (pathsinv0 _ _ _ (h x'))))). apply maponpathshomid1. apply (pathscomp0 _ _ _ _ eee ee). Defined. 


(* Here we consider the behavior of maponpaths in the case of a projection p with a section s. *)


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












(** Dependent sums (fibrations) **)


Inductive total2 (T:UU) (P:T -> UU) : UU := tpair: forall t:T, forall x: P t, total2 T P.


Definition pr21 (T:UU) (P:T -> UU) (z: total2 T P) : T := 
match z with 
tpair t x => t
end.  


Definition pr22 (T:UU) (P:T -> UU) (z: total2 T P) : P (pr21 _ _ z):=
match z with
tpair t x => x
end. 


Definition tppr (T:UU)(P:T -> UU)(x: total2 T P): paths _ x (tpair _ _ (pr21 _ _ x) (pr22 _ _ x)).
Proof. intros. induction x. apply idpath. Defined. 




(* Pairwise disjoint union. *)


Definition coprod (X Y:UU) := total2 bool (fun x:bool => match x with true => X | false => Y end).
Definition ii1 (X Y:UU): X -> coprod X Y := (fun x:X => tpair bool (fun x:bool => match x with true => X | false => Y end)  true x).
Definition ii2 (X Y:UU): Y -> coprod X Y := (fun y:Y => tpair bool (fun x:bool => match x with true => X | false => Y end)  false y).








(* Fibrations and paths. *)



Definition constr1 (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): total2 (P x -> P x') (fun f: P x -> P x' => (total2 (forall p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p))) (fun ee: forall p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p)) => forall pp: P x, paths _ (maponpaths _ _ (pr21 X P) _ _ (ee pp)) e))). 
Proof. intros. induction e. split with (fun p: P x => p). simpl. split with (fun p: P x => idpath _ _). unfold maponpaths. simpl. apply (fun pp: P x => idpath _ _ ). Defined. 


Definition transportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x -> P x' := pr21 _ _ (constr1 X P x x' e).

Lemma  transportfid (X:UU)(P:X -> UU)(x:X)(p: P x): paths _ (transportf _ P _ _ (idpath _ x) p) p.
Proof. intros. unfold transportf. unfold constr1.  simpl. apply idpath. Defined. 


Definition transportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x' -> P x := transportf _ P x' x (pathsinv0 _ _ _ e).


Lemma functtransportf (X:UU)(Y:UU)(f:X->Y)(P:Y->UU)(x:X)(x':X)(e: paths _ x x')(p: P (f x)): paths _ (transportf _ (fun x:X => P (f x)) x x' e p) (transportf _ P (f x) (f x') (maponpaths _ _ f _ _ e) p).
Proof.  intros.  induction e. apply idpath. Defined.   



(** First homotopy notions **)



Definition iscontr (T:UU) : UU := total2 T (fun cntr:T => forall t:T, paths T t cntr).

Definition iscontrpair (T:UU) (cntr: T) (e: forall t:T, paths T t cntr) : iscontr T := tpair T  (fun cntr:T => forall t:T, paths T t cntr) cntr e. 



Lemma contrl1 (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y y (f(g y))): iscontr X -> iscontr Y.
Proof. intros.  destruct X0.  set (y:= f t).  split with y.  intros.  
assert (e1: paths _ (f (g t0)) y). apply (maponpaths _ _ f _ _ (x (g t0))).
assert (e2: paths _ t0 (f (g t0))). apply (efg t0).
induction e2.  assumption.  Defined. 


Lemma contrl1' (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y): iscontr X -> iscontr Y.
Proof. intros. set (efg' := fun y:Y => pathsinv0 _ _ _ (efg y)).  apply contrl1 with X f g. assumption. assumption. Defined.

Lemma ifcontrthenconnected (X:UU)(is: iscontr X)(x:X)(x':X): paths _ x x'.
Proof. intros. unfold iscontr in is.  induction is. set (e:= x0 x). set (e':= pathsinv0 _ _ _ (x0 x')). apply (pathscomp0 _ _ _ _ e e'). Defined. 


Definition coconustot (T:UU) (t:T) := total2 T (fun t':T => paths T t' t).
Definition coconustotpair (T:UU) (t:T) (t':T) (e: paths T t' t):coconustot T t := tpair T (fun t':T => paths T t' t) t' e.

Lemma connectedcoconustot: forall T:Type, forall t:T, forall e1: coconustot T t, forall e2:coconustot T t, paths (coconustot T t) e1 e2.
Proof. intros. destruct e1. destruct x. destruct e2. destruct x. apply idpath. Defined. 

Lemma iscontrcoconustot (T:UU) (t:T) : iscontr (coconustot T t).
Proof. intros. unfold iscontr.  set (t0:= tpair _ (fun t':T => paths T t' t) t (idpath T t)).  split with t0. intros. apply  connectedcoconustot. Qed.



Definition coconusfromt (T:UU)(t:T) :=  total2 T (fun t':T => paths T t t').
Definition coconusfromtpair (T:UU) (t:T) (t':T) (e: paths T t t'):coconusfromt T t := tpair T (fun t':T => paths T t t') t' e.

Lemma connectedcoconusfromt: forall T:UU, forall t:T, forall e1: coconusfromt T t, forall e2:coconusfromt T t, paths (coconusfromt T t) e1 e2.
Proof. intros. destruct e1. destruct x. destruct e2. destruct x. apply idpath. Defined.

Lemma iscontrcoconusfromt (T:Type) (t:T) : iscontr (coconusfromt T t).
Proof. intros. unfold iscontr.  set (t0:= tpair _ (fun t':T => paths T t t') t (idpath T t)).  split with t0. intros. apply  connectedcoconusfromt. Qed.




Definition coconusf (T1:UU) (T2:UU) (f:T1 -> T2):= total2 T1 (fun t1:T1 => coconusfromt T2  (f t1)).
Definition coconusftriple (T1:UU) (T2:UU) (f:T1 -> T2) (t1:T1) (t2:T2) (e: paths _ (f t1) t2): coconusf _ _ f := tpair _ 
(fun t1:T1 => coconusfromt T2  (f t1)) t1 (coconusfromtpair T2 (f t1) t2 e). 


Definition pathsspace (T:UU) := coconusf _ _ (fun t:T => t).
Definition pathsspacetriple (T:UU) (t1:T)(t2:T)(e: paths _ t1 t2): pathsspace T := coconusftriple _ _ (fun t:T => t) t1 t2 e. 

Definition deltap (T:UU) : T -> pathsspace T := (fun t:T => pathsspacetriple _ t t (idpath _ t)). 




Definition hfiber (X:UU)(Y:UU)(f:X -> Y)(y:Y) : UU := total2 X (fun pointover:X => paths Y (f pointover) y). 
Definition hfiberpair  (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e: paths Y (f x) y): hfiber _ _ f y := tpair X  (fun pointover:X => paths Y (f pointover) y) x e.




Definition constr3 (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e1: paths _ (f x) y)(e2: paths _ (f x) y) (ee: paths _  e1 e2): paths _ (hfiberpair _ _ _ _ x e1) (hfiberpair _ _ _ _ x e2).
Proof. intros. induction ee. apply idpath.  Defined. 









(* Weak equivalences *)


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



Definition weqgf0  (T1:UU) (T2:UU) (f:T1-> T2) (is1: isweq _ _ f): forall t1:T1, paths T1 t1 ((invmap _ _ f is1) (f t1)).
Proof. intros. unfold isweq in is1. set (is2:= is1 (f t1)). set (e':= pr22 _ _ is2).  set (e'':= e' (tpair _ (fun c :  T1 => paths T2 (f c) (f t1))  t1 (idpath _ (f t1)))). unfold invmap.   apply (maponpaths _ _  (fun z: hfiber T1 T2 f (f t1) => pr21 _ _ z) _ _ e''). Defined.



Lemma iscontrxifiscontry (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr Y -> iscontr X.
Proof. intros. apply (contrl1 _ _ (invmap _ _ f is1) f (weqgf0 _ _ f is1) X0).  Defined. 




Definition weqgf (T1:UU) (T2:UU) (f:T1-> T2) (is1: isweq _ _ f): forall t1:T1, paths T1 ((invmap _ _ f is1) (f t1)) t1.
Proof. intros. apply (pathsinv0 _ _ _ (weqgf0 _ _ f is1 t1)). Defined.

Definition weqfg (T1:UU) (T2:UU) (f:T1-> T2) (is1: isweq _ _ f): forall t2:T2, paths T2 (f ((invmap _ _ f is1) t2)) t2.
Proof. intros. unfold invmap. simpl. unfold isweq in  is1. apply (pr22 _ _  (pr21 _ _  (is1 t2))). Defined.


Definition pathsweq1 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, forall y:Y, paths _ (f x) y -> paths _ x (invmap _ _ f is1 y):= pathssec1 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).


Definition pathsweq2 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, forall x':X, paths _ (f x) (f x') -> paths _ x x':= pathssec2 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq2id (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f): forall x:X, paths _ (pathsweq2 _ _ f is1 _ _ (idpath _ (f x))) (idpath _ x):= pathssec2id X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq3 (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f):  forall x:X, forall x':X, forall e: paths _ x x', paths _  (pathsweq2 _ _ f is1 _ _ (maponpaths _ _ f _ _ e)) e:= pathssec3 X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq4  (X: UU)(Y:UU)(f:X-> Y)(is1: isweq _ _ f):forall x:X, forall x':X, forall e: paths _ (f x) (f x'), paths _ (maponpaths _ _ f _ _ (pathsweq2 _ _ f is1 _ _ e)) e.  
Proof. intros. set (g:=invmap _ _ f is1). set (gf:= fun x:X => (g (f x))).  set (ee:= maponpaths _ _ g _ _ e). set (eee:= maponpathshomidinv _  gf (weqgf _ _ f is1) _ _ ee). assert (e1: paths _ (maponpaths _ _ f _ _ eee) e). assert (e2: paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ eee)) (maponpaths _ _ g _ _ e)). assert (e3: paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ eee)) (maponpaths _ _ gf _ _ eee)). apply maponpathsfuncomp. assert (e4: paths _ (maponpaths _ _ gf _ _ eee) ee). apply maponpathshomid2. apply (pathscomp0 _ _ _ _ e3 e4). 
set (s:= maponpaths _ _ g (f x) (f x')). set (p:= pathssec2 _ _ g f (weqfg _ _ f is1) (f x) (f x')). set (eps:= pathssec3 _ _ g f (weqfg _ _ f is1) (f x) (f x')).  apply (pathssec2 _ _ s p eps _ _ e2). assert (e4: paths _ (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' e)) (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee)))). apply (pathsinv0 _ _ _ (maponpaths _ _ (fun e0: paths _ (f x) (f x') => (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' e0))) _ _ e1)). assert (paths _  (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee)) eee). apply (pathsweq3 _ _ f is1). assert (e6: paths _ (maponpaths X Y f x x' (pathsweq2 X Y f is1 x x' (maponpaths X Y f x x' eee))) (maponpaths _ _ f _ _ eee)). apply (maponpaths _ _ (fun eee0: paths _ x x' => maponpaths _ _ f _ _ eee0) _ _ X0). set (e7:= pathscomp0 _ _ _ _ e4 e6). set (pathscomp0 _ _ _ _ e7 e1). assumption. Defined. 


 

(*Definition weqfgf (X:UU) (Y:UU) (f:X-> Y) (is1: isweq _ _ f): forall x:X, paths _ (weqfg _ _ f is1 (f x)) (maponpaths _ _ f _ _ (weqgf _ _ f is1 x)).
Proof. intros. unfold weqfg. unfold weqgf. unfold maponpaths.    simpl.*)







(* Functions between fibers defined by a path on the base are weak equivalences. *)






Lemma isweqtransportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportf X P x x' e).
Proof. intros. induction e. apply idisweq. Defined. 


Lemma isweqtransportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportb X P x x' e).
Proof. intros. apply (isweqtransportf _ _ _ _ (pathsinv0 _ _ _ e)). Defined. 





(* A type T:UU is contractible if and only if T -> unit is a weak equivalence. *)



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


Theorem unitiscontr: iscontr (unit).
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


Theorem ifcontrthenunit2: forall T:UU, (isweq T unit (fun t:T => tt)) -> (iscontr T).
Proof. intros. apply (iscontrxifiscontry T unit (fun t:T => tt) X unitiscontr). Defined. 




(* Theorem showing that a homotopy equivalence is a weak equivalence *)


Definition hfibergfr (X:UU) (Y:UU) (Z:UU) (f:X -> Y) (g: Y -> Z) (z:Z) : hfiber _ _ (fun x:X => g(f x)) z -> hfiber _ _ g z.
Proof. intros. destruct X0. apply (hfiberpair _ _ g z (f t) x).  Defined. 


Lemma constr2 (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y) (z: X): forall z0: (hfiber _ _ g z), total2 (hfiber _ _ (fun x:X => g(f x)) z) (fun z':_ => paths _ z0 (hfibergfr _ _ _ f g z z')). 
Proof. intros.  destruct z0. rename x into e. rename t into y. 

assert (eint: paths Y y (f z)).  assert (e0: paths Y (f(g y)) y). apply efg. assert (e1: paths Y (f(g y)) (f z)). apply (maponpaths _ _  f _ _ e). induction e1.  apply pathsinv0. assumption. 

set (int1:=constr1 Y (fun y:Y => paths X (g y) z) y (f z) eint). destruct int1.
set (int2:=hfiberpair _ _ (fun x0 : X => g (f x0)) z z (t e)).   split with int2.  apply x.  Defined. 


Lemma isweql1  (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths Y (f(g y)) y) (z: X): iscontr (hfiber _ _ (fun x:X => g(f x)) z) ->iscontr (hfiber _ _ g z).
Proof. intros. set (X1:= hfiber _ _ (fun x:X => g(f x)) z). set (Y1:= hfiber _ _ g z). set (f1:= hfibergfr _ _ _ f g z). set (g1:= fun z0:_ => pr21 _ _ (constr2 _ _ f g efg z z0)). 
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

Corollary isweqhom (X:UU)(Y:UU)(f1:X-> Y) (f2:X->Y) (h: forall x:X, paths _ (f1 x) (f2 x)): isweq _ _ f1 -> isweq _ _ f2.
Proof. intros. unfold isweq. intro. set (Y0:= X0 y).  apply (isweql2 _ _ f2 f1 h). assumption. Defined. 



Theorem gradth (X:UU)(Y:UU)(f:X->Y)(g:Y->X)(egf: forall x:X, paths _ (g (f x)) x)(efg: forall y:Y, paths _ (f (g y)) y ): isweq _ _ f.
Proof. intros.  unfold isweq.  intros. rename y into z. 
assert (iscontr (hfiber _ _ (fun y:Y => (f (g y))) z)). 
assert (efg': forall y:Y, paths _ y (f (g y))). intros. set (e1:= efg y). apply pathsinv0. assumption. 
apply (isweql2 Y Y (fun y:Y => (f (g y)))  (fun  y:Y => y)  efg' z (idisweq Y z)). 
apply (isweql1 _ _ g f egf z). assumption. 
Defined.
 


Corollary isweqinvmap (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f): isweq _ _ (invmap _ _ f is).
Proof. intros. set (invf:= invmap _ _ f is). assert (efinvf: forall y:Y, paths _ (f (invf y)) y). apply weqfg. 
assert (einvff: forall x:X, paths _ (invf (f x)) x). apply weqgf. apply (gradth _ _  invf f efinvf einvff). Defined. 


Corollary isweqcontr2 (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr X -> iscontr Y.
Proof. intros. apply (iscontrxifiscontry _ _ (invmap _ _ f is1) (isweqinvmap _ _ f is1)). assumption. Defined.

Corollary isweqmaponpaths (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f)(x:X)(x':X): isweq _ _ (maponpaths _ _ f x x').
Proof. intros. apply (gradth _ _ (maponpaths _ _ f x x') (pathsweq2 _ _ f is x x') (pathsweq3 _ _ f is x x')  (pathsweq4 _ _ f is x x')). Defined.  


(* Theorems showing that if any two of three functions f, g, gf are weak equivalences then so is the third - the 2-out-of-3 property. *)





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
Proof. intros. set (gf:= fun x:X => g (f x)). assert (int1: isweq _ _ gf). apply (isweqhom _ _ (fun x:X => x) gf  (fun x:X => (pathsinv0 _ _ _ (egf x)))). apply idisweq.  apply (twooutof3b _ _ _ f g X0 int1). Defined. 

Theorem twooutof3c (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z)(isf: isweq _ _ f)(isg: isweq _ _ g):isweq _ _  (fun x:X => g(f x)).
Proof. intros. set (gf:= fun x:X => g (f x)). set (invf:= invmap _ _ f isf). set (invg:= invmap _ _ g isg). set (invgf:= fun z:Z => invf (invg z)). assert (egfinvgf: forall x:X, paths _ (invgf (gf x)) x). unfold gf. unfold invgf.  intro.  assert (int1: paths _ (invf (invg (g (f x))))  (invf (f x))). apply (maponpaths _ _ invf _ _ (weqgf _ _ g isg (f x))). assert (int2: paths _ (invf (f x)) x). apply weqgf.  induction int1. assumption. 
assert (einvgfgf: forall z:Z, paths _ (gf (invgf z)) z).  unfold gf. unfold invgf. intro. assert (int1: paths _ (g (f (invf (invg z)))) (g (invg z))). apply (maponpaths _ _ g _ _ (weqfg _ _ f isf (invg z))).   assert (int2: paths _ (g (invg z)) z). apply (weqfg _ _ g isg z). induction int1. assumption. apply (gradth _ _ gf invgf egfinvgf einvgfgf). Defined. 






(* Theorems saying that for T:UU and P:T -> UU the homotopy fiber of the projection total2 T P -> T over t:T is weakly equivalent to P t. *)




Definition fibmap1 (T:UU) (P:T-> UU) (t:T): P t -> (hfiber _ _ (pr21 T P) t) := (fun z: P t => tpair _ _ (tpair T P t z) (idpath T t)).

Definition fibmap2 (T:UU) (P:T-> UU) (t:T): (hfiber _ _ (pr21 T P) t) -> P t:= fun z: hfiber  _ _ (pr21 T P) t =>
match z with 
tpair zz e => (transportf T P  (pr21 _ _ zz) t e (pr22 T P zz))
end.



Theorem fib1 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap1 T P t).
Proof. intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _ (fibmap1 T P t) (fibmap2 T P t) e1 e2). Defined. 

Theorem fib2 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap2 T P t).
Proof.  intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _  (fibmap2 T P t) (fibmap1 T P t) e2 e1). Defined. 



Corollary trivfib1 (T:UU) (P:T -> UU) (is1: forall t:T, iscontr (P t)) : isweq _ _ (pr21 T P).
Proof. intros. unfold isweq.  intro. set (isy:= is1 y). apply (iscontrxifiscontry _ _ (fibmap2 T P y) (fib2 T P y)). assumption. Defined. 


Corollary  coconusft1isweq (T1:UU)(T2:UU)(f:T1->T2): isweq (coconusf T1 T2 f) T1 (fun x:coconusf _ _ _ => pr21 _ _  x).
Proof. intros. assert (l1: forall t1:T1, iscontr (coconusfromt T2  (f t1))). intros. apply  iscontrcoconusfromt. apply trivfib1.  assumption.  Qed. 


Corollary isweqdeltap (T:UU) : isweq _ _ (deltap T).
Proof. intros. set (g:= (fun z: pathsspace T => pr21 _ _ z)). 
apply (twooutof3a _ _ _ (deltap T) g (idisweq T) (coconusft1isweq _ _ (fun t:T => t))). Defined.  






(********

Construction of the fibration sequence 

(hfiber f) -> (hfiber gf) -> (hfiber g)

for a composable pair f: X -> Y, g :Y -> Z where X Y Z are in  UU

*********)


Section hfiberseq.

Variables X Y Z: UU.
Variable f:X->Y.
Variable g:Y->Z.
Variable z:Z.
Variable ye: hfiber _ _ g z.

Let gf:= fun x:X => g (f x).
Let y:=pr21 _ _ ye.
Let e:=pr22 _ _ ye. 




Definition fibseqmap : hfiber _ _ (hfibergfr _ _ _ f g z) ye ->  hfiber _ _ f y.
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
 


Definition gzxmap1  : hfiber _ _ (hfibergfr _ _ _ f g z) ye -> hfiber _ _ (fun t: gzx => pr21 _ _ t) ye.
Proof. intros. destruct X0.  destruct t. rename x into e0. rename x0 into e'. rename t into x. set (int1:= tpair (hfiber _ _ g z) (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))) (hfiberpair _ _ g z (f x) e') (hfiberpair _ _ f  (f x) x (idpath _ (f x)))). split with int1. simpl. assumption. Defined. 


Definition gzxmap2 : hfiber _ _ (fun t: gzx => pr21 _ _ t) ye ->  hfiber _ _ (hfibergfr _ _ _ f g z) ye.
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
Proof. intros. set (h:=fibmap1 _ (fun ye: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ ye))) ye). simpl in h. assert (int1: isweq _ _ h). apply (fib1  _ (fun ye: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ ye))) ye).  apply (isweql3 _ _  h gzxmap4 (isweqgzxmap4l1) int1). Defined. 



Definition gzxhom12   (t: hfiber _ _ (fun t: gzx  => pr21 _ _ t) ye): paths _ (gzxmap1  (gzxmap2  t)) t. 
Proof. intros. assert (int1: paths _ (gzxmap4  (gzxmap1 (gzxmap2 t))) (gzxmap4 t)). apply gzxhom412. apply  (pathsweq2 _ _ (gzxmap4) (isweqgzxmap4 ) _ _ int1). Defined. 


Definition gzxhom21  (t:hfiber _ _ (hfibergfr _ _ _ f g z) ye) : paths _ (gzxmap2 (gzxmap1 t)) t. 
Proof. intros. destruct t.  destruct t. simpl. apply idpath. Defined. 


Lemma isweqgzxmap1  : isweq _ _ gzxmap1 .
Proof. intros. apply (gradth _  _ gzxmap1  gzxmap2  gzxhom21 gzxhom12 ).  Defined. 


Definition fibseqhom (u: hfiber _ _ (hfibergfr _ _ _ f g z) ye): paths _ (gzxmap4 (gzxmap1  u)) (fibseqmap  u).
Proof. intros. destruct u.   destruct t. simpl. apply idpath. Defined. 


Theorem fibseqth1 : isweq _ _ fibseqmap.
Proof.  intros. set (int1:= (fun u: hfiber _ _ (hfibergfr _ _ _ f g z) ye => (gzxmap4  (gzxmap1  u)))). assert (isweq _ _ int1). apply (twooutof3c _ _ _ gzxmap1  gzxmap4 isweqgzxmap1 isweqgzxmap4). apply (isweqhom _ _ int1 fibseqmap fibseqhom X0). Defined.



End hfiberseq. 



Corollary fibseqcor1 (X:UU)(Y:UU)(Z:UU)(f:X -> Y)(g:Y -> Z)(z:Z):(isweq _ _ f) -> (isweq _ _ (hfibergfr _ _ _ f g z)).
Proof. intros. unfold isweq.   intro. set (u:= fibseqmap X Y Z f g z y). assert (is1: isweq _ _ u). apply fibseqth1.  assert (int: iscontr (hfiber X Y f (pr21 Y (fun pointover : Y => paths Z (g pointover) z) y))). apply X0.  apply (iscontrxifiscontry _ _ u is1 int). Defined.





(* A fiber-wise morphism between total spaces is a weak equivalence if and only if all the morphisms between the fibers are weak equivalences. *)


Definition totalfun (X:UU)(P:X-> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x) := (fun z: total2 X P => tpair X Q (pr21 _ _ z) (f (pr21 _ _ z) (pr22 _ _ z))).


Theorem isweqtotaltofib (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
isweq _ _ (totalfun _ _ _ f) -> forall x:X, isweq _ _ (f x).
Proof. intros. set (totp:= total2 X P). set (totq := total2 X Q).  set (totf:= (totalfun _ _ _ f)). set (pip:= fun z: totp => pr21 _ _ z). set (piq:= fun z: totq => pr21 _ _ z). 

set (hfx:= hfibergfr _ _ _ totf piq x).  simpl in hfx. 
assert (isweq _ _ hfx). unfold isweq. intro. 
set (int:=fibseqmap _ _ _ totf piq x y). assert (isweq _ _ int). apply (fibseqth1 _ _ _ totf piq x y). destruct y. assert (is1: iscontr (hfiber _ _ totf t)). apply (X0 t). apply (iscontrxifiscontry _ _ int X1 is1).   
set (ip:= fibmap1 X P x). set (iq:= fibmap1 X Q x). set (h:= fun p: P x => hfx (ip p)).  assert (is2: isweq _ _ h). apply (twooutof3c _ _ _ ip hfx (fib1 X P x) X1). set (h':= fun p: P x => iq ((f x) p)). assert (ee: forall p:P x, paths _ (h p) (h' p)). intro. apply idpath.  assert (isweq _ _ h'). apply (isweqhom  _ _ h h' ee is2). apply (twooutof3a _ _ _ (f x) iq X2). apply (fib1 X Q x). Defined. 

Theorem isweqfibtototal (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
(forall x:X, isweq _ _ (f x)) -> isweq _ _ (totalfun _ _ _ f).
Proof. intros. set (fpq:= totalfun _ _ _ f). set (pr21p:= fun z: total2 X P => pr21 _ _ z). set (pr21q:= fun z: total2 X Q => pr21 _ _ z). unfold isweq. intro.  rename y into xq.  set (x:= pr21q xq). set (xqe:= hfiberpair _ _ pr21q x xq (idpath _ _)). set (hfpqx:= hfibergfr _ _ _ fpq pr21q x). 

assert (isint: iscontr (hfiber _ _ hfpqx xqe)). assert (isint1: isweq _ _ hfpqx). set (ipx:= fibmap1 X P x). set (iqx:= fibmap1 X Q x).   set (diag:= fun p:P x => (iqx ((f x) p))). assert (is2: isweq _ _ diag).  apply (twooutof3c _ _ _ (f x) iqx (X0 x) (fib1 X Q x)).  apply (twooutof3b _ _ _ ipx hfpqx (fib1 X P x) is2).  unfold isweq in isint1.  apply (isint1 xqe). 
set (intmap:= fibseqmap _ _ _ fpq pr21q x xqe). apply (isweqcontr2 _ _ intmap (fibseqth1 _ _ _ fpq pr21q x xqe) isint). 
Defined.








(* Given X Y in UU, P:Y -> UU and f: X -> Y we get a function fpmap: total2 X (P f) -> total2 Y P. The main theorem of this section asserts that the homotopy fiber of fpmap over yp:total Y P is naturally weakly equivalent to the homotopy fiber of f over pr21 yp. In particular, if f is a weak equivalence then so is fpmap. *)


Definition fpmap (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU) : total2 X (fun x:X => P (f x)) -> total2 Y P := 
(fun z:total2 X (fun x:X => P (f x)) => tpair Y P (f (pr21 _ _ z)) (pr22 _ _ z)).


Definition hffpmap2 (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU):  total2 X (fun x:X => P (f x)) -> total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)).
Proof. intros. set (u:= fpmap _ _ f P X0).  split with u. set (x:= pr21 _ _ X0).  split with x. simpl. apply idpath. Defined.


Definition hfiberfpmap (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): hfiber _ _ (fpmap _ _ f P) yp -> hfiber _ _ f (pr21 _ _ yp).
Proof. intros. set (int1:= hfibergfr _ _ _ (hffpmap2 _ _ f P) (fun u: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => (pr21 _ _ u)) yp).  set (phi:= fibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). apply (phi (int1 X0)).   Defined. 



Lemma centralfiber (X:UU)(P:X -> UU)(x:X): isweq _ _ (fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p).
Proof. intros. set (f:= fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p). set (g:= fun z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) => transportf X P (pr21 _ _ (pr21 _ _ z)) x (pathsinv0 _ _ _ (pr22 _ _ (pr21 _ _ z))) (pr22 _ _ z)).  

assert (efg: forall  z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)), paths _ (f (g z)) z). intro. destruct z. destruct t.   simpl. induction x1. simpl. apply idpath. 

assert (egf: forall p: P x , paths _ (g (f p)) p).  intro. apply idpath.  

apply (gradth _ _  f g egf efg). Qed. 


Lemma isweqhff (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU): isweq _ _ (hffpmap2 _ _ f P). 
Proof. intros. set (int:= total2 X (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)))). set (intpair:= tpair X (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)))).  set (toint:= fun z: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => intpair (pr21 _ _ (pr22 _ _ z)) (tpair _  (fun u: coconusfromt _ (f (pr21 _ _ (pr22 _ _ z))) => P (pr21 _ _ u)) (coconusfromtpair _ _ (pr21 _ _ (pr21 _ _ z)) (pr22 _ _ (pr22 _ _ z))) (pr22 _ _ (pr21 _ _ z)))). set (fromint:= fun z: int => tpair _ (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) (tpair Y P (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr22 _ _ (pr22 _ _ z))) (hfiberpair _ _ f (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr21 _ _ z) (pr22 _ _ (pr21 _ _ (pr22 _ _ z))))). assert (fromto: forall u:(total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))), paths _ (fromint (toint u)) u). simpl in toint. simpl in fromint. simpl. intro. destruct u. destruct x. destruct t. simpl. unfold toint. unfold fromint. simpl. apply idpath. assert (tofrom: forall u:int, paths _ (toint (fromint u)) u). intro. destruct u. destruct x. destruct t0. simpl in x. simpl. unfold fromint. unfold toint. simpl. apply idpath. assert (is: isweq _ _ toint). apply (gradth _ _ toint fromint fromto tofrom).  clear tofrom. clear fromto.  clear fromint.

set (h:= fun u: total2 X (fun x:X => P (f x)) => toint ((hffpmap2 _ _ f P) u)). simpl in h. 

assert (l1: forall x:X, isweq _ _ (fun p: P (f x) => tpair _  (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)) (coconusfromtpair _ _ (f x) (idpath _  (f x))) p)). intro. apply (centralfiber Y P (f x)).  

assert (isweq _ _ h). apply (isweqfibtototal X (fun x:X => P (f x))  (fun x:X => total2 (coconusfromt _ (f x)) (fun u: coconusfromt _ (f x) => P (pr21 _ _ u))) (fun x:X => (fun p: P (f x) => tpair _  (fun u: coconusfromt _ (f x) => P (pr21 _ _ u)) (coconusfromtpair _ _ (f x) (idpath _  (f x))) p))). assumption.   

apply (twooutof3a _ _ _ (hffpmap2 _ _ f P) toint X0 is). Defined. 




Theorem isweqhfiberfp (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): isweq _ _ (hfiberfpmap _ _ f P yp).
Proof. intros. set (int1:= hfibergfr _ _ _ (hffpmap2 _ _ f P) (fun u: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => (pr21 _ _ u)) yp). assert (is1: isweq _ _ int1). apply fibseqcor1. apply isweqhff. set (phi:= fibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). assert (is2: isweq _ _ phi). apply (fib2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). apply (twooutof3c _ _ _ int1 phi is1 is2).   Defined. 


Corollary isweqfp (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU): isweq _ _ f -> isweq _ _ (fpmap _ _ f P).
Proof. intros. unfold isweq.   intro. unfold isweq in X0.  set (h:=hfiberfpmap _ _ f P y). assert (isweq _ _ h). apply isweqhfiberfp. assert (is: iscontr (hfiber X Y f (pr21 _ _ y))). apply X0. apply (iscontrxifiscontry _ _  h X1 is). Defined. 







(* Basics about h-levels. *)


Fixpoint isofhlevel (n:nat) (X:UU): UU:=
match n with
O => iscontr X |
S m => forall x:X, forall x':X, (isofhlevel m (paths _ x x'))
end.


Theorem hlevelretract (n:nat)(X:UU)(Y:UU)(p:X -> Y)(s:Y ->X)(eps: forall y:Y, paths _  (p (s y)) y): (isofhlevel n X) -> (isofhlevel n Y).
Proof. intro. induction n. intros. apply (contrl1' _ _ p s eps X0). 
intros. unfold isofhlevel. intros. unfold isofhlevel in X0. assert (is: isofhlevel n (paths _ (s x) (s x'))).  apply X0. set (s':= maponpaths _ _ s x x'). set (p':= pathssec2 _ _ s p eps x x'). set (eps':= pathssec3 _ _ s p eps x x'). apply (IHn _ _ p' s' eps' is). Defined. 

Corollary  hlevelweqf (n:nat)(X:UU)(Y:UU)(f:X -> Y)(is: isweq _ _ f): (isofhlevel n X) -> (isofhlevel n Y).
Proof. intros.  apply (hlevelretract n _ _ f (invmap _ _ f is) (weqfg _ _ f is)). assumption. Defined. 

Corollary  hlevelweqb (n:nat)(X:UU)(Y:UU)(f:X -> Y)(is: isweq _ _ f): (isofhlevel n Y) -> (isofhlevel n X).
Proof. intros.  apply (hlevelretract n _ _ (invmap _ _ f is) f (weqgf _ _ f is)). assumption. Defined. 


Definition isaprop (X:UU): UU := isofhlevel (S O) X. 

Lemma isaprop1 (X:UU): (isaprop X) -> X -> (iscontr X).
Proof. intros. unfold iscontr. split with X1. intro.  unfold isaprop in X0.  unfold isofhlevel in X0.  set (is:= X0 t X1). apply (pr21 _ _ is). 
Defined. 


Lemma isweqimplimpl (X:UU)(Y:UU)(f:X->Y)(g:Y->X)(isx: isaprop X)(isy: isaprop Y): isweq _ _ f.
Proof. intros. assert (isx0: forall x:X, paths _ (g (f x)) x). intro.  assert (iscontr X). apply (isaprop1 X isx x).  apply (ifcontrthenconnected X X0 (g (f x)) x). assert (isy0: forall y:Y, paths _ (f (g y)) y). intro. assert (iscontr Y). apply (isaprop1 Y isy y). apply (ifcontrthenconnected Y X0 (f (g y)) y). apply (gradth _ _ f g isx0 isy0).  Defined. 

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros. induction x. Defined. 

Theorem isapropunit: isaprop unit.
Proof. unfold isaprop. intros. unfold isofhlevel. intros. 
assert (c:paths unit x x'). induction x. induction x'. eapply idpath.
assert (forall g:paths unit x x', paths _ g c). intros. assert (e:paths (paths unit x x') c c).   apply idpath. induction c. induction x. apply unitl3. apply (iscontrpair _ c X). Defined.  


Theorem ifcontrthenaprop (X:UU): (iscontr X) -> (isaprop X).
Proof. intros. set (f:= fun x:X => tt). assert (is: isweq _ _ f). apply isweqcontrtounit.  assumption. apply (hlevelweqb (S O) X unit f is).  apply isapropunit. Defined. 


Theorem hlevelsincl (n:nat) (T:UU) : isofhlevel n T -> isofhlevel (S n) T.
Proof. intro.   induction n. intro. apply (ifcontrthenaprop T). intro.  intro. change (forall t1 t2:T, isofhlevel (S n) (paths _ t1 t2)). intros. change (forall t1 t2 : T, isofhlevel n (paths _ t1 t2)) in X. set (XX := X t1 t2). apply (IHn _ XX).  Defined.



Definition isaset (X:UU): UU := isofhlevel (S (S O)) X. 

Lemma isaset1 (X:UU): (forall x:X, iscontr (paths _ x x)) -> isaset X.
Proof. intros. unfold isaset. unfold isofhlevel. intros.   induction x0. set (is:= X0 x). apply ifcontrthenaprop. assumption.  Defined. 

Lemma isaset2 (X:UU): (isaset X) -> (forall x:X, iscontr (paths _ x x)).
Proof. intros. unfold isaset in X0. unfold isofhlevel in X0.  change (forall (x x' : X) (x0 x'0 : paths X x x'), iscontr (paths (paths X x x') x0 x'0))  with (forall (x x':X),  isaprop (paths _ x x')) in X0.  apply (isaprop1 _ (X0 x x) (idpath _ x)). Defined.

(** to move up **)

Definition initmap (X:UU) : empty -> X.
Proof. intros.  induction X0. Defined. 


Theorem onefiber (X:UU)(P:X -> UU)(x:X)(c: forall x':X, coprod (paths _ x x') (P x' -> empty)):
isweq _ _ (fun p: P x => tpair X P x p).
Proof. intros.  

set (f:= fun p: P x => tpair _ _ x p). 

set (cx := c x). 
set (cnew:=  fun x':X  =>
match cx with 
tpair true x0 =>
match c x' with 
tpair true ee => tpair _ _ true (pathscomp0 _ _ _ _ (pathsinv0 _ _ _ x0) ee)|
tpair false phi => tpair _ _ false phi
end |
tpair false phi => c x'
end).

set (g:= fun pp: total2 X P => 
match (cnew (pr21 _ _ pp)) with
tpair  true e => transportb X P _ _ e (pr22 _ _ pp) |
tpair  false phi =>  initmap _ (phi (pr22 _ _ pp))
end).


assert (efg: forall pp: total2 X P, paths _ (f (g pp)) pp).  intro. induction pp. set (cnewt:= cnew t).  unfold g. unfold f. simpl. change (cnew t) with cnewt. induction cnewt.  induction t0. apply (pathsinv0 _ _ _ (pr21 _ _ (pr22 _ _ (constr1 X P t x (pathsinv0 _ _ _ x1))) x0)). induction (x1 x0). 

 
set (cnewx:= cnew x). 
assert (e1: paths _ (cnew x) cnewx). apply idpath. 
unfold cnew in cnewx. change (c x) with cx in cnewx.  
induction cx. induction t. 
assert (e: paths _ (cnewx) (ii1 _ _ (idpath _ x))).  apply (maponpaths _ _ (ii1 (paths X x x) (P x -> empty)) _ _ (pathsinv0l1 _ _ _ x0)). 




assert (egf: forall p: P x, paths _ (g (f p)) p).  intro. simpl in g. unfold g.  unfold f.   simpl.   

set (ff:= fun cc:coprod (paths X x x) (P x -> empty) => 
match cc with
     | tpair t phi =>
         match
           t as t0
           return
             (match t0 with
              | true => paths X x x
              | false => P x -> empty
              end -> P x)
         with
         | true => fun phi0 : paths X x x => transportb X P x x phi0 p
         | false => fun phi0 : P x -> empty => initmap (P x) (phi0 p)
         end phi
     end). 
assert (ee: paths _ (ff (cnewx)) (ff (ii1 (paths X x x) (P x -> empty) (idpath X x)))).  apply (maponpaths _ _ ff _ _ e). 
assert (eee: paths _  (ff (ii1 (paths X x x) (P x -> empty) (idpath X x))) p). apply idpath.  fold (ff (cnew x)). 
assert (e2: paths _ (ff (cnew x)) (ff cnewx)). apply (maponpaths _ _ ff _ _ e1). 
apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e2 ee) eee).
apply (gradth _ _ f g egf efg).

unfold isweq.  intro. induction y. set (ct:= c t). induction ct. induction t0. induction x2.  induction (x0 x1). induction (x2 x1). Defined. 


Theorem isasetifdec (X:UU): (forall (x x':X), coprod (paths _ x x') (paths _ x x' -> empty)) -> isaset X.
Proof. intro. intro. 
assert (l1: forall x:X, iscontr (paths _ x x)). intro.  set (f:= fun e: paths _ x x => coconusfromtpair _ x x e). 
assert (is: isweq _ _ f). apply (onefiber X (fun x':X => paths _ x x') x (X0 x)).
assert (is2: iscontr (coconusfromt _ x)). apply iscontrcoconusfromt. 
apply (iscontrxifiscontry _ _ f is). assumption. apply isaset1. assumption. Defined. 




Fixpoint curry (x:bool) : UU := 
match x with
false => empty|
true => unit
end.



Theorem nopathstruetofalse: paths _ true false -> empty.
Proof. intro.  apply (transportf _ curry _ _ X tt).  Defined.

Corollary nopathsfalsetotrue: paths _ false true -> empty.
Proof. intro. apply (transportb _ curry _ _ X tt). Defined. 

Theorem isdecbool: forall x:bool, forall x':bool, coprod (paths _ x x') (paths _ x x' -> empty).
Proof. intros. induction x. induction x'. apply (ii1 _ _ (idpath _ true)). apply (ii2 _ _ nopathstruetofalse). induction x'.  apply (ii2 _ _ nopathsfalsetotrue). apply (ii1 _ _ (idpath _ false)). Defined. 


Theorem isasetbool: isaset bool.
Proof. apply (isasetifdec _ isdecbool). Defined. 


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
 


Theorem isdecnat:  forall x:nat, forall x':nat, coprod (paths _ x x') (paths _ x x' -> empty).
Proof. intro. induction x. intro. induction x'. apply (ii1 _ _ (idpath _ O)). apply (ii2 _ _ (nopathsOtoSx x')). intro. induction x'. apply (ii2 _ _ (nopathsSxtoO x)). set (is:= IHx x').  induction is. induction t. apply (ii1 _ _ (maponpaths _ _ S _ _ x0)). apply (ii2 _ _ (noeqinjS _ _ x0)). Defined.


Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdec _ isdecnat). Defined. 



(* Basics about h-levels of functions. *)


Definition isofhlevelf (n:nat)(X:UU)(Y:UU)(f:X -> Y): UU := forall y:Y, isofhlevel n (hfiber _ _ f y).









(* Several simple lemmas which are used to compensate for the absence of eta-reduction in the current version of Coq. *)


Axiom etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths _ f (fun t:T => f t). 

Lemma isweqetacorrection (T:UU)(P:T -> UU): isweq _ _ (fun f: forall t:T, P t => (fun t:T => f t)).
Proof. intros.  apply (isweqhom _ _ (fun f: forall t:T, P t => f) (fun f: forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => etacorrection _ P f) (idisweq _)). Defined. 

Lemma etacorrectiononpaths (T:UU)(P:T->UU)(s1:forall t:T, P t)(s2:forall t:T, P t): paths _ (fun t:T => s1 t) (fun t:T => s2 t)-> paths _ s1 s2. 
Proof. intros. set (ec:= fun s:forall t:T, P t => (fun t:T => s t)). set (is:=isweqetacorrection T P). apply (pathsweq2 _ _ ec is s1 s2 X). Defined. 

Definition etacor (X:UU)(Y:UU)(f:X -> Y):paths _ f (fun x:X => f x) := etacorrection X (fun T:X => Y) f.

Lemma etacoronpaths (X:UU)(Y:UU)(f1:X->Y)(f2:X->Y):paths _ (fun x:X => f1 x) (fun x:X => f2 x) -> paths _ f1 f2. 
Proof. intros. set (ec:= fun f:X->Y => (fun x:X => f x)). set (is:=isweqetacorrection X (fun x:X => Y)). apply (pathsweq2 _ _ ec is f1 f2 X0). Defined.


(* Sections of "double fibration" P: T -> UU, PP: forall t:T, P t -> UU and pairs of sections. *)

Definition totaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) -> forall x:X, total2 (P x) (PP x).
Proof. intros. induction X0. split with (t x). apply (x0 x). Defined.


Definition foralltototal  (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU):  (forall x:X, total2 (P x) (PP x)) -> total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)).
Proof. intros. split with (fun x:X => pr21 _ _ (X0 x)). apply (fun x:X => pr22 _ _ (X0 x)). Defined.

Lemma lemmaeta1 (X:UU)(P:X->UU)(Q:(forall x:X, P x) -> UU)(s0: forall x:X, P x)(q: Q (fun x:X => (s0 x))): paths (total2 _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x)))) (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) s0 q) (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) (fun x:X => (s0 x)) q). 
Proof. intros. set (ff:= fun tp:total2 _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) => tpair _ _ (fun x:X => pr21 _ _ tp x) (pr22 _ _ tp)). assert (isweq _ _ ff).  apply (isweqfp _ _ (fun s: forall x:X, P x => (fun x:X => (s x))) Q (isweqetacorrection X P)). assert (ee: paths _ (ff (tpair (forall x : X, P x)
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


(* The construction of the second homotopy 

Definition foralltototaltoforall(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss: forall x:X, total2 (P x) (PP x)): paths _ (totaltoforall _ _ _ (foralltototal _ _ _ ss)) ss.

whichn implies that foralltototal and totaltoforall are weak equivalences, is done in u012 since  it requires functional extensionality for section. *)



(* The maps between section spaces (dependent products) defined by a family of maps P x -> Q x and by the map Y -> X. *)

Definition maponsec (X:UU)(P:X -> UU)(Q:X-> UU)(f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) := 
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).







(* Conjecture triv (T:UU): paths _ T T. *)


