Require Export u1.
Require Export u0.



(* The following definitions establish the hierarchy of universes such that

UU0=u0.UU
UU1=u1.UU

UU0:UU1 and UU0 is a subtype of UU1 *)


Definition j01:UU -> u1.UU:= fun T:UU => T. 
Definition j11:u1.UU -> u1.UU:=fun T:u1.UU => T.

Definition UU0:=j11 UU.
Definition UU1:=u1.UU.


(* Note: by the current agreement in Coq, the names introduced in u0, as the last module to be imported, "shadow" the names introduced in u1 so that, for example, paths is the same as u0.paths and UU is the same as u0.UU *)







Definition eqweqmap (T1:UU0) (T2:UU0) : (u1.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU0, forall T2:UU0, u1.isweq (u1.paths Type T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f): u1.paths _ T1 T2 := u1.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).


Definition weqpathsweq (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f):u1.paths _ (eqweqmap _ _ (weqtopaths _ _ f is)) (weqpair _ _ f is) := u1.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).

(* Conjecture: univalenceaxiom is equivalent to two axioms 

Axiom weqtopaths0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f): paths1 _ T1 T2.

Axiom weqpathsweq0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ f is)) (weqpair0 _ _ f is).

*)




(* Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u1.paths _ x x'): isweq _ _ (u1.transportf X P x x' e).
Proof. intros. induction e.  apply idisweq. Defined.

Lemma isweqtransportb10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u1.paths _ x x'): isweq _ _ (u1.transportb X P x x' e).
Proof. intros. apply (isweqtransportf10 _ _ _ _ (u1.pathsinv0 _ _ _ e)). Defined. 


Lemma l1  (X0:UU0)(X0':UU0)(ee: u1.paths _ X0 X0')(P:UU0 -> UU0)(pp': P X0')(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p):paths _ (R X0 X0' (pr21 _ _ (eqweqmap _ _ ee)) (pr22 _ _ (eqweqmap _ _ ee)) pp') (u1.transportb UU0 P X0 X0' ee pp').
Proof. intro. intro. intro. intro. intro. induction ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb  (P:UU0 -> UU0)(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p): forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u,  forall p':P X', paths _ (R X X' u is p') (u1.transportb UU0  P X X' (weqtopaths _ _ u is) p').  
Proof. intros. set (uis:=weqpair _ _ u is). set (uv:=weqtopaths _ _ u is).   set (v:=eqweqmap _ _ uv). 

assert (e:u1.paths _ v uis). unfold weqtopaths in uv.  apply (u1.weqfg  (u1.paths UU0 X X') (weq X X')  (eqweqmap X X') (univalenceaxiom X X') uis).

assert (ee:u1.paths _ (R X X' (pr21 _ _ v) (pr22 _ _ v) p') (R X X' u is p')). set (R':= fun vis:weq X X' => R X X' (pr21 _ _ vis) (pr22 _ _ vis) p'). assert (ee':u1.paths _ (R' v) (R' uis)). apply (u1.maponpaths (weq X X') (P X) R' _ _ e). assumption. 

induction ee. apply l1. assumption. Defined.

Corollary isweqweqtransportb (P:UU0 -> UU0)(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p): forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, isweq _ _ (fun p': P X' => R X X' u is p').
Proof. intros. assert (e:forall p':P X', paths _ (R X X' u is p') (u1.transportb UU0 P X X' (weqtopaths _ _ u is) p')). apply weqtransportb. assumption. assert (ee :forall p':P X', paths _  (u1.transportb UU0 P X X' (weqtopaths _ _ u is) p') (R X X' u is p')). intro.  apply (pathsinv0 _ _ _ (e p')). clear e. 

assert (is1:isweq _ _ (u1.transportb UU0 P X X' (weqtopaths _ _ u is))). apply isweqtransportb10.  
apply (isweqhom _ _ (u1.transportb UU0 P X X' (weqtopaths X X' u is)) (fun p' : P X' => R X X' u is p') ee is1).  Defined. 



    

(* Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)




Theorem isweqcompwithweq (X:UU0)(X':UU0)(u:X->X')(is:isweq _ _ u)(Y:UU0): isweq _ _ (fun f:X'->Y => (fun x:X => f (u x))).
Proof. intros. 
set (P:= fun X0:UU0 => (X0 -> Y)). 
set (R:= fun X0:UU0 => (fun X0':UU0 => (fun u0:X0 -> X0' => (fun is0:isweq _ _ u0 => (fun  f:P X0'  => (fun x:X0 => f (u0 x))))))). 
set (r:= fun X0:UU0 => (fun f:X0 -> Y => pathsinv0 _ _ _ (etacor X0 Y f))).
apply (isweqweqtransportb P R r X X' u is). Defined.




(* Proof of the functional extensionality for functions *)





Lemma eqcor0 (X:UU0)(X':UU0)(u:X->X')(is:isweq _ _ u)(Y:UU0)(f1:X'->Y)(f2:X'->Y):  (paths _ (fun x:X => f1 (u x))  (fun x:X => f2 (u x))) -> paths _ f1 f2. 
Proof. intros. apply (pathsweq2 _ _ (fun f:X'->Y => (fun x:X => f (u x))) (isweqcompwithweq _ _ u is Y) f1 f2). assumption.  Defined. 


Lemma apathpr1topr2 (T:UU0) : paths _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z)).
Proof. intro. apply (eqcor0 _ _  (deltap T) (isweqdeltap T) _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z))  (idpath _ (fun t:T => t))). Defined.     


Theorem funextfun (X:UU0)(Y:UU0)(f1:X->Y)(f2:X->Y)(e: forall x:X, paths _ (f1 x) (f2 x)): paths _ f1 f2.
Proof. intros. set (f:= (fun x:X => pathsspacetriple Y (f1 x) (f2 x) (e x))).  set (g1:= (fun z:pathsspace Y => pr21 _ _ z)). set (g2:= fun z: pathsspace Y => pr21 _ _ (pr22 _ _ z)). assert (e': paths _ g1 g2). apply (apathpr1topr2 Y). assert (ee:paths _ (fun x:X => f1 x) (fun x:X => f2 x)). apply (maponpaths2b _ _ _ f g1 g2 e').  apply etacoronpaths.  assumption. Defined. 




(* More results on types of h-level 1 (propositions). *)


Lemma iscontrtounit (T:UU0) :iscontr (T -> unit).
Proof. intros. set (cntr:= (fun t:T => tt)). split with cntr. intros. assert (e: forall f1: T -> unit, forall t:T,  paths _ (f1 t) tt). intros. induction (f1 t0). apply idpath. apply (funextfun T unit t cntr (e t)). Defined. 


Theorem isapropneg (X:UU0): isaprop (X -> empty).
Proof. intro. unfold isaprop. unfold isofhlevel.  
assert (is1:forall (f g: X -> empty), forall x:X, paths _ (f x) (g x)). intros.  apply initmap. apply (f x). 
assert (is2: forall (f g:X -> empty), paths _ f g). intros.  apply (funextfun _ _ f g (is1 f g)). apply (isaprop2 _ is2). Defined.

Lemma isapropaninvprop (X:UU0): isaninvprop X -> isaprop X.
Proof. intros. 
assert (is1: isaprop (dneg X)). apply (isapropneg (neg X)). 
apply (hlevelweqb (S O) _ _ (adjev X) X0 is1). Defined. 


Theorem isaninvpropneg (X:UU0): isaninvprop (neg X).
Proof. intros. 
set (f:= adjev (neg X)). set (g:= negf _ _ (adjev X)). set (is1:= isapropneg X). set (is2:= isapropneg (dneg X)). apply (isweqimplimpl _ _ f g is1 is2).  Defined.


Theorem isapropxornotx (X:UU0): (isaprop X) -> (isaprop (coprod X (X-> empty))).
Proof. intros. 
assert (forall (x x': X), paths _ x x'). apply (isaprop2' _ X0).  
assert (forall (x x': coprod X (X -> empty)), paths _ x x'). intros.  
induction x. induction t. induction x'.  induction t. apply (maponpaths _ _ (fun x:X => ii1 _ _ x) _ _ (X1 x x0)).    
apply (initmap _ (x0 x)). induction x'. induction t.  apply (initmap _ (x x0)). 
assert (e: paths _ x x0). apply (isaprop2' _ (isapropneg X) x x0). apply (maponpaths _ _ (fun f: X -> empty => ii2 _ _ f) _ _ e).
apply (isaprop2 _ X2).  Defined. 


Theorem isaninv1 (X:UU0): isdecprop X  -> isaninvprop X.
Proof. unfold isaninvprop. intros. rename X0 into is.  set (is1:= pr21 _ _ is). set (is2:= pr22 _ _ is). simpl in is2. 
assert (adjevinv: dneg X -> X). intros.  induction is2. induction t. assumption. induction (X0 x). 
assert (is3: isaprop (dneg X)). apply (isapropneg (X -> empty)). apply (isweqimplimpl _ _ (adjev X) adjevinv is1 is3). Defined. 











(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y *)


Definition locsplit (X:UU0)(Y:UU0)(f:X -> Y):= forall y:Y, coprod (hfiber _ _ f y) (hfiber _ _ f y -> empty).

Definition dnegimage (X:UU0)(Y:UU0)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber _ _ f y)).

Definition xtodnegimage (X:UU0)(Y:UU0)(f:X -> Y): X -> dnegimage _ _ f:= fun x:X => tpair _ _ (f x) ((adjev _) (hfiberpair _ _ f (f x) x (idpath _ (f x)))). 

Definition locsplitsec (X:UU0)(Y:UU0)(f:X->Y)(ls: locsplit _ _ f): dnegimage _ _ f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with 
tpair true z => pr21 _ _ z|
tpair false phi => initmap _ (psi phi)
end
end.


Definition locsplitsecissec  (X:UU0)(Y:UU0)(f:X->Y)(ls: locsplit _ _ f)(u:dnegimage _ _ f): paths _ (xtodnegimage _ _ f (locsplitsec _ _ f ls u)) u.
Proof. intros.  set (p:= xtodnegimage _ _ f). set (s:= locsplitsec _ _ f ls).  
assert (paths _ (pr21 _ _ (p (s u))) (pr21 _ _ u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst. induction t0. simpl. apply (pr22 _ _ x0). induction (x x0). 




Definition negimage (X:UU0)(Y:UU0)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber _ _ f y)).

Definition imsum (X:UU0)(Y:UU0)(f:X -> Y): coprod (dnegimage _ _ f) (negimage _ _ f) -> Y:= fun u:_ =>
match y with
tpair true z => pr21 _ _ z|
tpair false z => pr21 _ _ z
end.


 






(* Some results on types with an isolated point. *)


Definition isisolated (X:UU0)(x:X):= forall x':X, coprod (paths _ x x') (paths _ x x' -> empty).


Definition complement (X:UU0)(x:X):= total2 X (fun x':X => (paths _ x x' -> empty)).
Definition complementpair (X:UU0)(x:X):= tpair X (fun x':X => (paths _ x x' -> empty)).


Definition recompl (X:UU0)(x:X): coprod (complement X x) unit -> X := fun u:_ =>
match u with
tpair true x0 => pr21 _ _ x0|
tpair false tt => x
end.

Definition recomplinv (X:UU0)(x:X)(is: isisolated X x): X -> coprod (complement X x) unit:=
fun x':X => match (is x') with
tpair true e => ii2 _ _ tt|
tpair false phi => ii1 _ _ (complementpair _ _ x' phi)
end.


Theorem isweqrecompl (X:UU0)(x:X)(is:isisolated X x): isweq _ _ (recompl X x).
Proof. intros. set (f:= recompl X x). set (g:= recomplinv X x is). unfold recomplinv in g. simpl in g. 
assert (egf: forall u: coprod  (complement X x) unit, paths _ (g (f u)) u). intro. induction u. induction t. unfold f. unfold recompl. induction x0.  unfold g. simpl. induction (is t). induction t0.  induction (x0 x1). 
assert (e: paths _ x1 x0). apply (isaprop2' _ (isapropneg (paths _ x t))). induction e.  apply idpath. 
unfold f. unfold g. simpl. induction x0. induction (is x). induction t. apply idpath. induction (x0 (idpath _ x)).
assert (efg: forall x':X, paths _ (f (g x')) x'). intro.   induction (is x'). induction t. induction x0. unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x).  induction t. simpl. apply idpath. induction (x0 (idpath _ x)).  unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x').  induction t. induction (x0 x1). simpl. apply idpath.
apply (gradth _ _ f g egf efg). Defined.


Lemma isolatedtoisolated (X:UU0)(Y:UU0)(f:X -> Y)(is1:isweq _ _ f)(x:X)(is2: isisolated _ x): isisolated _ (f x).
Proof.  intros. unfold isisolated. intro. rename x' into y.  set (g:=invmap _ _ f is1). set (x':= g y). induction (is2 x').  induction t. apply (ii1 _ _ (pathsweq1' _ _ f is1 x y x0)). 
assert (phi: paths _ (f x) y -> empty). 
assert (psi: (paths _ x (g y) -> empty) -> (paths _ (f x) y -> empty)). intro. intro.  apply (X0  (pathsweq1 _ _ f is1 x y X1)). apply (psi x0). apply (ii2 _ _ phi). Defined.


Definition maponcomplements (X:UU0)(Y:UU0)(f:X -> Y)(is1: isweq _ _ f)(x:X)(is2: isisolated _ x): complement X x -> complement Y (f x).
Proof. intros. set (Q:= fun y:Y => (paths _ (f x) y -> empty)). set (map1:= fpmap _ _ f Q).
assert (isw1: isweq _ _ map1). apply  isweqfpmap. assumption.   
assert (mp: forall x':X, (paths _ x x' -> empty) -> (paths _ (f x) (f x') -> empty)). intro. intro. intro. apply (X1 (pathsweq2 _ _ f is1 _ _ X2)). set (map2:= totalfun X (fun x':X => (paths _ x x' -> empty)) (fun x':X => Q (f x')) mp).
assert (isw2: forall x':X, isweq _ _ (mp x')). intro. 
assert (mpinv: (paths Y (f x) (f x') -> empty)->(paths X x x' -> empty)). apply (noneql1 X Y f x x').  apply (isweqimplimpl _ _ (mp x') mpinv (isapropneg _) (isapropneg _)).
assert (isw3: isweq _ _ map2). apply (isweqfibtototal _ _ _ mp isw2). 

























(* Finite Sets *)



Fixpoint standardnel(n:nat):UU0:= match n with
O => empty|
S m => coprod (standardnel m) unit
end. 


Definition isofnel (n:nat)(X:UU0):UU1 := forall PP:UU0->UU0, (forall Y:UU0, isaprop (PP Y)) -> (PP (standardnel n)) -> (PP X). 

Lemma isapropisofnel (n:nat)(X:UU0): u1.isaprop (isofnel n X).
Proof. intros. 
assert (is1: forall PP:UU0->UU0, isaprop ( (forall Y:UU0, isaprop (PP Y)) -> (PP (standardnel n)) -> (PP X))).
intro. assert (is2: forall a: (forall Y:UU0, isaprop (PP Y)), forall b:  (PP (standardnel n)), isaprop (PP X)). intros. apply (a X). apply (u1.







Lemma isofnel1 (n n':nat)(X:UU0): isonel

Definition fset := u1.total2 UU0 (fun X:UU0 => (u1.total2 nat (fun n:nat => isofnel n X))).

Definition fcurry (X:fset): UU0 := u1.pr21 _ _ X.

Definition numofel (X:fset): nat:= u1.pr21 _ _ (u1.pr22 _ _ X). 

Definition isfset (X:UU0) :UU1 := u1.total2 nat (fun n:nat => isofnel n X).
 

Theorem isapropisfset (X:UU0): u1.isaprop (isfset X).
Proof. intros. unfold isfset. set (P:= fun n:nat => isofnel n X). set (f:= fun  





(* Some other constructions *)

Lemma ifcontrthenunit: forall T:UU0, (iscontr T) -> u1.paths _ T unit. 
Proof. intros.  apply isweqcontrtounit in X. apply weqtopaths in X. assumption. Defined. 





















(* End of the file u01.v *)






