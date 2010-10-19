
Require Export uuu. 


Definition UU:=Type.
Definition juuutouu:UUU -> UU:= fun T:_ => T.

Definition initmap (X:UU) : empty -> X.
Proof. intros.  induction X0. Defined. 





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



Definition dirprod (X:UU)(Y:UU):= total2 X (fun x:X => Y).
Definition dirprodpair (X:UU)(Y:UU):= tpair X (fun x:X => Y).






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

Lemma contrl2 (X:UU)(is: iscontr X)(x:X)(x':X): paths _ x x'.
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



Lemma hfibertriangle1 (X Y:UU)(f:X -> Y)(y:Y)(xe1 xe2: hfiber _ _ f y)(e: paths _ xe1 xe2): paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (maponpaths (hfiber _ _ f y) X  (pr21 _ _ ) _ _ e)) (pr22 _ _ xe2)).
Proof. intros. destruct e.  simpl. apply idpath. Defined. 


Lemma hfibertriangle2 (X Y:UU)(f:X -> Y)(y:Y)(xe1 xe2: hfiber _ _ f y)(ee: paths _ (pr21 _ _ xe1) (pr21 _ _ xe2))(eee: paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ ee) (pr22 _ _ xe2))): paths _ xe1 xe2.
Proof. intros. destruct xe1. destruct xe2.   simpl in eee. simpl in ee. destruct ee. simpl in eee. apply (maponpaths _ _ (fun e: paths _ (f t) y => hfiberpair _ _ f y t e) _ _ eee). Defined. 


Definition constr3 (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e1: paths _ (f x) y)(e2: paths _ (f x) y) (ee: paths _  e1 e2): paths _ (hfiberpair _ _ _ _ x e1) (hfiberpair _ _ _ _ x e2).
Proof. intros. destruct ee. apply idpath.  Defined. 









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


(* We now define different homotopies and maps between the paths spaces corresponding to a weak equivalence. What may look like unnecessary complexity in the  definition of weqgf is due to the fact that the "naive" definition, that of weqgf00, needs to be corrected in order for the lemma weqfgf to hold. *)



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










(* Weak equivalences between contractible types. *)



Lemma iscontrxifiscontry (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr Y -> iscontr X.
Proof. intros. apply (contrl1 _ _ (invmap _ _ f is1) f (weqgf0 _ _ f is1) X0).  Defined. 




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
Proof. intros. set (gf:= fun x:X => g (f x)). assert (int1: isweq _ _ gf). apply (isweqhomot _ _ (fun x:X => x) gf  (fun x:X => (pathsinv0 _ _ _ (egf x)))). apply idisweq.  apply (twooutof3b _ _ _ f g X0 int1). Defined. 

Theorem twooutof3c (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z)(isf: isweq _ _ f)(isg: isweq _ _ g):isweq _ _  (fun x:X => g(f x)).
Proof. intros. set (gf:= fun x:X => g (f x)). set (invf:= invmap _ _ f isf). set (invg:= invmap _ _ g isg). set (invgf:= fun z:Z => invf (invg z)). assert (egfinvgf: forall x:X, paths _ (invgf (gf x)) x). unfold gf. unfold invgf.  intro.  assert (int1: paths _ (invf (invg (g (f x))))  (invf (f x))). apply (maponpaths _ _ invf _ _ (weqgf _ _ g isg (f x))). assert (int2: paths _ (invf (f x)) x). apply weqgf.  induction int1. assumption. 
assert (einvgfgf: forall z:Z, paths _ (gf (invgf z)) z).  unfold gf. unfold invgf. intro. assert (int1: paths _ (g (f (invf (invg z)))) (g (invg z))). apply (maponpaths _ _ g _ _ (weqfg _ _ f isf (invg z))).   assert (int2: paths _ (g (invg z)) z). apply (weqfg _ _ g isg z). induction int1. assumption. apply (gradth _ _ gf invgf egfinvgf einvgfgf). Defined. 



Definition weqcomp (X Y Z:UU): (weq X Y) -> (weq Y Z) -> (weq X Z) := fun u: weq X Y => fun v: weq Y Z => weqpair _ _ (fun x:X => (pr21 _ _ v (pr21 _ _ u x))) (twooutof3c _ _ _ _ _ (pr22 _ _ u) (pr22 _ _ v)). 















(* Basics about fibration sequences. 

By a pre-fibration sequence we mean a structure of the form 
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


(* The first four fibration sequences associated with a function. *)


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






(* Theorems saying that for T:UU and P:T -> UU the homotopy fiber of the projection total2 T P -> T over t:T is weakly equivalent to P t. *)




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


Corollary  coconusft1isweq (T1:UU)(T2:UU)(f:T1->T2): isweq (coconusf T1 T2 f) T1 (fun x:coconusf _ _ _ => pr21 _ _  x).
Proof. intros. assert (l1: forall t1:T1, iscontr (coconusfromt T2  (f t1))). intros. apply  iscontrcoconusfromt. apply trivfib1.  assumption.  Qed. 


Corollary isweqdeltap (T:UU) : isweq _ _ (deltap T).
Proof. intros. set (g:= (fun z: pathsspace T => pr21 _ _ z)). 
apply (twooutof3a _ _ _ (deltap T) g (idisweq T) (coconusft1isweq _ _ (fun t:T => t))). Defined.  


Corollary familyfibseq (T:UU)(P:T->UU)(t:T): isfibseq (P t) (total2 T P) T (fun p: P t => tpair _ _ t p) (pr21 T P) t (fun p: P t => idpath _ t).
Proof. intros. unfold isfibseq. unfold ezmap.  apply isweqfibmap1. Defined.






(********

Construction of the fibration sequence 

(hfiber f) -> (hfiber gf) -> (hfiber g)

for a composable pair f: X -> Y, g :Y -> Z where X Y Z are in  UU

*********)


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



(* Main corollaries of the constructions of hfibersseq. *)


Corollary isweqhfibersgftog (X:UU)(Y:UU)(Z:UU)(f:X -> Y)(g:Y -> Z)(z:Z):(isweq _ _ f) -> (isweq _ _ (hfibersgftog _ _ _ f g z)).
Proof. intros. unfold isweq.   intro. set (u:= hfibersinvezmap X Y Z f g z y). assert (is1: isweq _ _ u). apply isweqhfibersinvezmap.  assert (int: iscontr (hfiber X Y f (pr21 Y (fun pointover : Y => paths Z (g pointover) z) y))). apply X0.  apply (iscontrxifiscontry _ _ u is1 int). Defined.


Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)):  hfiber _ _ (fun x:X => g (f x)) z:= pr21 _ _ (hfibersezmap _ _ _ f g z ye xe). 


Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)): paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye := pr22 _ _ (hfibersezmap _ _ _ f g z ye xe).



(* There are the follwing alternative definitions of hfibersftogf and hfibseqez:

Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z): hfiber _ _ f (pr21 _ _ ye) -> hfiber _ _ (fun x:X => g (f x)) z:= fun xe:_ => hfiberpair _ _ (fun x:X => g (f x)) z (pr21 _ _ xe) (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye)).


Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)): paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye := hfibertriangle2 _ _ g z (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye (pr22 _ _ xe) (idpath _ (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye))).

However I do not know whether the are equivalent to the ones given below or whether one can prove that the resulting pre-fibration sequence is a fibration sequence. *)


Corollary isfibseqhfibers (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z): isfibseq (hfiber _ _ f (pr21 _ _ ye)) (hfiber _ _ (fun x:X => g (f x)) z) (hfiber _ _ g z)  (hfibersftogf _ _ _ f g z ye) (hfibersgftog _ _ _ f g z) ye (hfibersez _ _ _ f g z ye).
Proof. intros.  unfold isfibseq. apply isweqhfibersezmap. Defined.













(* A fiber-wise morphism between total spaces is a weak equivalence if and only if all the morphisms between the fibers are weak equivalences. *)


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








(* Given X Y in UU, P:Y -> UU and f: X -> Y we get a function fpmap: total2 X (P f) -> total2 Y P. The main theorem of this section asserts that the homotopy fiber of fpmap over yp:total Y P is naturally weakly equivalent to the homotopy fiber of f over pr21 yp. In particular, if f is a weak equivalence then so is fpmap. *)


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

apply (gradth _ _  f g egf efg). Qed. 


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










(* Several simple lemmas which are used to compensate for the absence of eta-reduction in the current version of Coq. *)


Axiom etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths _ f (fun t:T => f t). 

Lemma isweqetacorrection (T:UU)(P:T -> UU): isweq _ _ (fun f: forall t:T, P t => (fun t:T => f t)).
Proof. intros.  apply (isweqhomot _ _ (fun f: forall t:T, P t => f) (fun f: forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => etacorrection _ P f) (idisweq _)). Defined. 

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


(* The construction of the second homotopy 

Definition foralltototaltoforall(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss: forall x:X, total2 (P x) (PP x)): paths _ (totaltoforall _ _ _ (foralltototal _ _ _ ss)) ss.

whichn implies that foralltototal and totaltoforall are weak equivalences, is done in u012 since  it requires functional extensionality for sections (dependent functions). *)



(* The maps between section spaces (dependent products) defined by a family of maps P x -> Q x and by the map Y -> X. *)

Definition maponsec (X:UU)(P:X -> UU)(Q:X-> UU)(f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) := 
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).



(* Some basic construction related to the adjoint evaluation function X -> ((X -> Y) -> Y). *)


Definition adjev (X Y:UU): X -> ((X -> Y)->Y) := fun x:X => fun f:_ => f x.

Definition adjev2 (X Y:UU): (((X -> Y) -> Y) ->Y) -> (X -> Y)  := fun phi:_ => (fun x:X => phi (fun f:X -> Y => f x)).

Definition adjevretract (X Y:UU): forall f: X-> Y, paths _ (adjev2 _ _ (adjev (X -> Y) Y f)) f.
Proof. intros. unfold adjev2. unfold adjev. apply (pathsinv0 _ _ _ (etacorrection _ _ f)). Defined. 




(* Basic results on negation and double negation. *)


Definition neg (X:UU):= X -> empty.

Definition negf (X:UU)(Y:UU)(f:X -> Y): (neg Y) -> (neg X):= fun phi:Y -> empty => fun x:X => phi (f x).

Definition dneg (X:UU):= (X-> empty)->empty.

Definition dnegf (X:UU)(Y:UU)(f:X->Y): (dneg X) -> (dneg Y):= negf _ _ (negf _ _ f).

Definition todneg (X:UU): X -> (dneg X):= adjev X empty. 

Definition negadjev (X:UU): dneg (neg X) -> neg X := negf _ _  (todneg X).

Lemma dneganddnegl1 (X:UU)(Y:UU): dneg X -> dneg Y -> (X -> neg Y) -> empty.
Proof. intros. assert (dneg X -> neg Y). apply (fun xx: dneg X => negadjev _ (dnegf _ _ X2 xx)).  apply (X1 (X3 X0)). Defined.

Lemma dneganddnegimpldneg (X:UU)(Y:UU): dneg X -> dneg Y -> dneg (dirprod X Y).
Proof. intros. unfold dneg. intro. set (X3:= fun x:X => fun y:Y => X2 (dirprodpair _ _ x y)). apply (dneganddnegl1 _ _ X0 X1 X3). Defined.





Definition isaninvprop (X:UU):= isweq _ _  (todneg X).

Definition invimpl (X:UU)(is: isaninvprop X): (dneg X) -> X:= invmap _ _ (todneg X) is. 






















(* Basics about h-levels. *)


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



Theorem ifcontrthenaprop (X:UU): (iscontr X) -> (isofhlevel (S O) X).
Proof. intros. set (f:= fun x:X => tt). assert (is: isweq _ _ f). apply isweqcontrtounit.  assumption. apply (isofhlevelweqb (S O) X unit f is).  apply isapropunit. Defined. 


Theorem hlevelsincl (n:nat) (T:UU) : isofhlevel n T -> isofhlevel (S n) T.
Proof. intro.   induction n. intro. apply (ifcontrthenaprop T). intro.  intro. change (forall t1 t2:T, isofhlevel (S n) (paths _ t1 t2)). intros. change (forall t1 t2 : T, isofhlevel n (paths _ t1 t2)) in X. set (XX := X t1 t2). apply (IHn _ XX).  Defined.


Corollary isofhlevelcontr (n:nat)(X:UU): iscontr X -> isofhlevel n X.
Proof. intro. induction n. intros. assumption. 
intros. simpl. intros. assert (is: iscontr (paths _ x x')). apply (ifcontrthenaprop _ X0 x x'). apply (IHn _ is). Defined.

Lemma iscontraprop1 (X:UU): (isofhlevel (S O) X) -> (X -> (iscontr X)).
Proof. intros. unfold iscontr. split with X1. intro.  unfold isofhlevel in X0.  set (is:= X0 t X1). apply (pr21 _ _ is). 
Defined. 

Lemma iscontraprop1inv (X:UU): (X -> iscontr X) -> (isofhlevel (S O) X).
Proof. intros. assert (X -> isofhlevel (S O) X). intro.  apply (hlevelsincl O _ (X0 X1)). apply (isofhlevelsn O _ X1). Defined.






(* Basics about h-levels of functions. *)


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













(* Basics on pairwise coproducts (disjoint unions). I.  *)



Inductive coprod (X Y:UU) := ii1: X -> coprod X Y | ii2: Y -> coprod X Y.


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

Definition coprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y'): coprod X Y -> coprod X' Y' := fun xy: coprod X Y =>
match xy with
ii1 x => ii1 _ _ (f x)|
ii2 y => ii2 _ _ (g y)
end. 


Theorem isweqcoprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y')(isf:isweq _ _ f)(isg: isweq _ _ g): isweq _ _ (coprodf _ _ _ _ f g).
Proof. intros. set (f1:= coprodtoboolsum X Y). set (f2:= totalfun bool (boolsumfun X Y) (boolsumfun X' Y') (fun t:bool => match t with true => f | false => g end)). set (f3:= boolsumtocoprod X' Y'). 
assert (h: forall xy:coprod X Y, paths _ (f3 (f2 (f1 xy))) (coprodf _ _ _ _ f g xy)).  intro. destruct xy. apply idpath. apply idpath.
assert (is1: isweq _ _ f2). apply (isweqfibtototal bool  (boolsumfun X Y) (boolsumfun X' Y') (fun t:bool => match t with true => f | false => g end) (fun t:bool => match t with true => isf | false => isg end)).
assert (is2: isweq _ _ (fun xy: coprod X Y => f2 (f1 xy))). apply (twooutof3c _ _ _ _ _ (isweqcoprodtoboolsum X Y) is1).
apply  (isweqhomot _ _ _ _ h (twooutof3c _ _ _ _ _  is2 (isweqboolsumtocoprod X' Y'))). Defined.













(* Theorem saying that if a fibration has only one non-empty fiber then the total space is weakly equivalent to this fiber. *)



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

















(* Basics about types of h-level 1 - "propositions". *)


Definition isaprop (X:UU): UU := isofhlevel (S O) X. 

Lemma isweqimplimpl (X:UU)(Y:UU)(f:X->Y)(g:Y->X)(isx: isaprop X)(isy: isaprop Y): isweq _ _ f.
Proof. intros. assert (isx0: forall x:X, paths _ (g (f x)) x). intro.  assert (iscontr X). apply (iscontraprop1 X isx x).  apply (contrl2 X X0 (g (f x)) x). assert (isy0: forall y:Y, paths _ (f (g y)) y). intro. assert (iscontr Y). apply (iscontraprop1 Y isy y). apply (contrl2 Y X0 (f (g y)) y). apply (gradth _ _ f g isx0 isy0).  Defined. 

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros. induction x. Defined. 


Lemma proofirrelevance (X:UU): (isaprop X) -> (forall (x x':X), paths _ x x'). 
Proof. intros. unfold isaprop in X0. unfold isofhlevel in X0.   apply (pr21 _ _ (X0 x x')). Defined. 


Lemma invproofirrelevance (X:UU): (forall (x x':X), paths _ x x') -> isaprop X.
Proof. intros. unfold isaprop. unfold isofhlevel.  intro.  
assert (is: iscontr X).  split with x. intro.  apply (X0 t x). assert (is1: isaprop X).  apply ifcontrthenaprop. assumption.   
unfold isaprop in is1. unfold isofhlevel in is1.  apply (is1 x). Defined. 



(* Basics about "decidable"  propositions. Continued in u01.v after the proof of functional extensionality for functions. *)


Definition isdecprop (X:UU):= dirprod (isaprop X) (coprod X (X -> empty)).











(* Basics about types of h-level 2 - "sets". *)




Definition isaset (X:UU): UU := isofhlevel (S (S O)) X. 

Lemma isaset1 (X:UU): (forall x:X, iscontr (paths _ x x)) -> isaset X.
Proof. intros. unfold isaset. unfold isofhlevel. intros.   induction x0. set (is:= X0 x). apply ifcontrthenaprop. assumption.  Defined. 

Lemma isaset2 (X:UU): (isaset X) -> (forall x:X, iscontr (paths _ x x)).
Proof. intros. unfold isaset in X0. unfold isofhlevel in X0.  change (forall (x x' : X) (x0 x'0 : paths X x x'), iscontr (paths (paths X x x') x0 x'0))  with (forall (x x':X),  isaprop (paths _ x x')) in X0.  apply (iscontraprop1 _ (X0 x x) (idpath _ x)). Defined.



Definition isdeceq (X:UU): UU :=  forall (x x':X), coprod (paths _ x x') (paths _ x x' -> empty).

Theorem isasetifdeceq (X:UU): (isdeceq X) -> isaset X.
Proof. intro. intro. unfold isdeceq in X0.  
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

Theorem isdeceqbool: isdeceq bool.
Proof. unfold isdeceq. intros. induction x. induction x'. apply (ii1 _ _ (idpath _ true)). apply (ii2 _ _ nopathstruetofalse). induction x'.  apply (ii2 _ _ nopathsfalsetotrue). apply (ii1 _ _ (idpath _ false)). Defined. 


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
Proof. unfold isdeceq. intro. induction x. intro. induction x'. apply (ii1 _ _ (idpath _ O)). apply (ii2 _ _ (nopathsOtoSx x')). intro. induction x'. apply (ii2 _ _ (nopathsSxtoO x)). set (is:= IHx x').  induction is.  apply (ii1 _ _ (maponpaths _ _ S _ _ x0)). apply (ii2 _ _ (noeqinjS _ _ y)). Defined.


Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdeceq _ isdeceqnat). Defined. 





(* Basics about function of h-level 1 (inclusions). *)

Definition isincl (X Y:UU)(f:X -> Y):= isofhlevelf (S O) _ _ f.

Lemma iscontrhfiberforincl (X:UU)(Y:UU)(f:X -> Y): isincl _ _ f -> (forall x:X, iscontr (hfiber _ _ f (f x))).
Proof. intros. unfold isofhlevelf in X0. set (isy:= X0 (f x)).  apply (iscontraprop1 _ isy (hfiberpair _ _ f (f x) x (idpath _ (f x)))). Defined.


Lemma isweqonpathsincl (X:UU)(Y:UU)(f:X -> Y)(is: isincl _ _ f)(x x':X): isweq _ _ (maponpaths _ _ f x x').
Proof. intros. apply (isofhlevelfonpaths O _ _ f x x' is). Defined.


Definition invmaponpathsincl (X Y:UU)(f:X -> Y) (is: isincl _ _ f)(x x':X): paths _ (f x) (f x') -> paths _ x x':= invmap _ _ (maponpaths _ _ f x x') (isweqonpathsincl _ _ f is x x').


Lemma isinclweqonpaths (X Y:UU)(f:X -> Y): (forall x x':X, isweq _ _ (maponpaths _ _ f x x')) -> isincl _ _ f.
Proof. intros.  apply (isofhlevelfsn O _ _ f X0). Defined.






(* Pairwise coproducts. II. *)



Lemma negeqii1ii2 (X Y:UU)(x:X)(y:Y): neg (paths _ (ii1 _ _ x) (ii2 _ _ y)).
Proof. intros. unfold neg. intro. apply (nopathstruetofalse (maponpaths _ _ (coprodtobool _ _)  _ _ X0)).  Defined.


Theorem isaninclii1 (X Y:UU): isofhlevelf (S O) _ _ (ii1 X Y).
Proof. intros. set (f:= ii1 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun x:X => (g (f x))). set (gf':= fun x:X => tpair _ (boolsumfun X Y) true x). 
assert (h: forall x:X , paths _ (gf' x) (gf x)). intro. apply idpath. 
assert (is1: isofhlevelf (S O) _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) true (isasetbool true true)).
assert (is2: isofhlevelf (S O) _ _ gf). apply (isofhlevelfhomot (S O) _ _ gf' gf h is1).  
apply (isofhlevelff (S O) _ _ _ _ _ is2 (isofhlevelfweq (S (S O)) _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 


Theorem isaninclii2 (X Y:UU): isofhlevelf (S O) _ _ (ii2 X Y).
Proof. intros. set (f:= ii2 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun y:Y => (g (f y))). set (gf':= fun y:Y => tpair _ (boolsumfun X Y) false y). 
assert (h: forall y:Y , paths _ (gf' y) (gf y)). intro. apply idpath. 
assert (is1: isofhlevelf (S O) _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) false (isasetbool false false)).
assert (is2: isofhlevelf (S O) _ _ gf). apply (isofhlevelfhomot (S O) _ _ gf' gf h is1).  
apply (isofhlevelff (S O) _ _ _ _ _ is2 (isofhlevelfweq (S (S O)) _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 



(* Finite sets I. *)



Fixpoint stn (n:nat):UU:= match n with
O => empty|
S m => coprod (stn m) unit
end.











(* End of the file u0.v *)


