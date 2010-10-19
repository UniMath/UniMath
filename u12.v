

Require Export u2.
Require Export u1.



(* The following definitions establish the hierarchy of universes such that

UU0=u0.UU
UU1=u2.UU

UU0:UU1 and UU0 is a subtype of UU1 *)


Definition j01:UU -> u2.UU:= fun T:UU => T. 
Definition j11:u2.UU -> u2.UU:=fun T:u2.UU => T.

Definition UU0:=j11 UU.
Definition UU1:=u2.UU.


(* Note: by the current agreement in Coq, the names introduced in u0, as the last module to be imported, "shadow" the names introduced in u1 so that, for example, paths is the same as u0.paths and UU is the same as u0.UU *)







Definition eqweqmap (T1:UU0) (T2:UU0) : (u2.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU0, forall T2:UU0, u2.isweq (u2.paths Type T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f): u2.paths _ T1 T2 := u2.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).


Definition weqpathsweq (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f):u2.paths _ (eqweqmap _ _ (weqtopaths _ _ f is)) (weqpair _ _ f is) := u2.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).

(* Conjecture: univalenceaxiom is equivalent to two axioms 

Axiom weqtopaths0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f): paths1 _ T1 T2.

Axiom weqpathsweq0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ f is)) (weqpair0 _ _ f is).

*)




(* Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u2.paths _ x x'): isweq _ _ (u2.transportf X P x x' e).
Proof. intros. induction e.  apply idisweq. Defined.

Lemma isweqtransportb10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u2.paths _ x x'): isweq _ _ (u2.transportb X P x x' e).
Proof. intros. apply (isweqtransportf10 _ _ _ _ (u2.pathsinv0 _ _ _ e)). Defined. 


Lemma l1  (X0:UU0)(X0':UU0)(ee: u2.paths _ X0 X0')(P:UU0 -> UU0)(pp': P X0')(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p):paths _ (R X0 X0' (pr21 _ _ (eqweqmap _ _ ee)) (pr22 _ _ (eqweqmap _ _ ee)) pp') (u2.transportb UU0 P X0 X0' ee pp').
Proof. intro. intro. intro. intro. intro. induction ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb  (P:UU0 -> UU0)(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p): forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u,  forall p':P X', paths _ (R X X' u is p') (u2.transportb UU0  P X X' (weqtopaths _ _ u is) p').  
Proof. intros. set (uis:=weqpair _ _ u is). set (uv:=weqtopaths _ _ u is).   set (v:=eqweqmap _ _ uv). 

assert (e:u2.paths _ v uis). unfold weqtopaths in uv.  apply (u2.weqfg  (u2.paths UU0 X X') (weq X X')  (eqweqmap X X') (univalenceaxiom X X') uis).

assert (ee:u2.paths _ (R X X' (pr21 _ _ v) (pr22 _ _ v) p') (R X X' u is p')). set (R':= fun vis:weq X X' => R X X' (pr21 _ _ vis) (pr22 _ _ vis) p'). assert (ee':u2.paths _ (R' v) (R' uis)). apply (u2.maponpaths (weq X X') (P X) R' _ _ e). assumption. 

induction ee. apply l1. assumption. Defined.

Corollary isweqweqtransportb (P:UU0 -> UU0)(R: forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (fun x:X => x) (idisweq X) p) p): forall X:UU0, forall X':UU0, forall u:X -> X', forall is: isweq X X' u, isweq _ _ (fun p': P X' => R X X' u is p').
Proof. intros. assert (e:forall p':P X', paths _ (R X X' u is p') (u2.transportb UU0 P X X' (weqtopaths _ _ u is) p')). apply weqtransportb. assumption. assert (ee :forall p':P X', paths _  (u2.transportb UU0 P X X' (weqtopaths _ _ u is) p') (R X X' u is p')). intro.  apply (pathsinv0 _ _ _ (e p')). clear e. 

assert (is1:isweq _ _ (u2.transportb UU0 P X X' (weqtopaths _ _ u is))). apply isweqtransportb10.  
apply (isweqhomot _ _ (u2.transportb UU0 P X X' (weqtopaths X X' u is)) (fun p' : P X' => R X X' u is p') ee is1).  Defined. 



    

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
assert (is2: forall (f g:X -> empty), paths _ f g). intros.  apply (funextfun _ _ f g (is1 f g)). apply (invproofirrelevance _ is2). Defined.

Corollary isapropdneg (X:UU0): isaprop (dneg X).
Proof. intro. apply (isapropneg (neg X)). Defined.

Lemma isapropaninvprop (X:UU0): isaninvprop X -> isaprop X.
Proof. intros. 
apply (isofhlevelweqb (S O) _ _ (todneg X) X0 (isapropdneg X)). Defined. 


Theorem isaninvpropneg (X:UU0): isaninvprop (neg X).
Proof. intros. 
set (f:= todneg (neg X)). set (g:= negf _ _ (todneg X)). set (is1:= isapropneg X). set (is2:= isapropneg (dneg X)). apply (isweqimplimpl _ _ f g is1 is2).  Defined.


Theorem isapropxornotx (X:UU0): (isaprop X) -> (isaprop (coprod X (X-> empty))).
Proof. intros. 
assert (forall (x x': X), paths _ x x'). apply (proofirrelevance _ X0).  
assert (forall (x x': coprod X (X -> empty)), paths _ x x'). intros.  
induction x.  induction x'.   apply (maponpaths _ _ (fun x:X => ii1 _ _ x) _ _ (X1 x x0)).    
apply (initmap _ (y x)). induction x'.   apply (initmap _ (y x)). 
assert (e: paths _ y y0). apply (proofirrelevance _ (isapropneg X) y y0). apply (maponpaths _ _ (fun f: X -> empty => ii2 _ _ f) _ _ e).
apply (invproofirrelevance _ X2).  Defined. 


Theorem isaninv1 (X:UU0): isdecprop X  -> isaninvprop X.
Proof. unfold isaninvprop. intros. rename X0 into is.  set (is1:= pr21 _ _ is). set (is2:= pr22 _ _ is). simpl in is2. 
assert (adjevinv: dneg X -> X). intros.  induction is2.  assumption. induction (X0 y). 
assert (is3: isaprop (dneg X)). apply (isapropneg (X -> empty)). apply (isweqimplimpl _ _ (todneg X) adjevinv is1 is3). Defined. 











(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y *)


Definition locsplit (X:UU0)(Y:UU0)(f:X -> Y):= forall y:Y, coprod (hfiber _ _ f y) (hfiber _ _ f y -> empty).

Definition dnegimage (X:UU0)(Y:UU0)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber _ _ f y)).
Definition dnegimageincl (X Y:UU0)(f:X -> Y):= pr21 Y (fun y:Y => dneg(hfiber _ _ f y)).

Definition xtodnegimage (X:UU0)(Y:UU0)(f:X -> Y): X -> dnegimage _ _ f:= fun x:X => tpair _ _ (f x) ((todneg _) (hfiberpair _ _ f (f x) x (idpath _ (f x)))). 

Definition locsplitsec (X:UU0)(Y:UU0)(f:X->Y)(ls: locsplit _ _ f): dnegimage _ _ f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with 
ii1 z => pr21 _ _ z|
ii2 phi => initmap _ (psi phi)
end
end.


Definition locsplitsecissec  (X Y:UU0)(f:X->Y)(ls: locsplit _ _ f)(u:dnegimage _ _ f): paths _ (xtodnegimage _ _ f (locsplitsec _ _ f ls u)) u.
Proof. intros.  set (p:= xtodnegimage _ _ f). set (s:= locsplitsec _ _ f ls).  
assert (paths _ (pr21 _ _ (p (s u))) (pr21 _ _ u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst.  simpl. apply (pr22 _ _ x0). induction (x y).  
assert (is: isofhlevelf (S O) _ _ (dnegimageincl _ _ f)). apply (isofhlevelfpr21 (S O) _ _ (fun y:Y => isapropdneg (hfiber _ _ f y))).  
assert (isw: isweq _ _ (maponpaths _ _ (dnegimageincl _ _ f) (p (s u)) u)). apply (isofhlevelfonpaths O _ _ _ _ _ is). 
apply (invmap _ _ _ isw X0). Defined.



Definition negimage (X:UU0)(Y:UU0)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber _ _ f y)).
Definition negimageincl (X Y:UU0)(f:X -> Y):= pr21 Y (fun y:Y => neg(hfiber _ _ f y)).


Definition imsum (X:UU0)(Y:UU0)(f:X -> Y): coprod (dnegimage _ _ f) (negimage _ _ f) -> Y:= fun u:_ =>
match u with
ii1 z => pr21 _ _ z|
ii2 z => pr21 _ _ z
end.


 


(* Some results on complements to a point *)


Definition complement (X:UU0)(x:X):= total2 X (fun x':X => neg (paths _ x' x)).
Definition complementpair (X:UU0)(x:X):= tpair X (fun x':X => neg (paths _ x' x)).


Definition recompl (X:UU0)(x:X): coprod (complement X x) unit -> X := fun u:_ =>
match u with
ii1 x0 => pr21 _ _ x0|
ii2 tt => x
end.

Definition maponcomplementsincl (X:UU0)(Y:UU0)(f:X -> Y)(is: isofhlevelf (S O) _ _ f)(x:X): complement X x -> complement Y (f x):= fun x0':_ =>
match x0' with
tpair x' neqx => tpair _ _ (f x') (negf _ _ (invmaponpathsincl _ _ _ is x' x) neqx)
end.

Definition maponcomplementsweq (X Y:UU0)(f:X -> Y)(is: isweq _ _ f)(x:X):= maponcomplementsincl _ _ f (isofhlevelfweq (S O) _ _ f is) x.


Theorem isweqmaponcomplements (X Y:UU0)(f:X -> Y)(is: isweq _ _ f)(x:X): isweq _ _ (maponcomplementsweq _ _ f is x).
Proof. intros.  set (is1:= isofhlevelfweq (S O) _ _ f is).   set (map1:= totalfun X (fun x':X => neg (paths _ x' x)) (fun x':X => neg (paths _ (f x') (f x))) (fun x':X => negf _ _ (invmaponpathsincl _ _ _ is1 x' x))). set (map2:= fpmap _ _ f (fun y:Y => neg (paths _ y (f x)))). 
assert (is2: forall x':X, isweq  _ _ (negf _ _ (invmaponpathsincl _ _ _ is1 x' x))). intro. 
set (invimpl:= (negf _ _ (maponpaths _ _ f x' x))). apply (isweqimplimpl _ _ (negf _ _ (invmaponpathsincl _ _ _ is1 x' x)) (negf _ _ (maponpaths _ _ f x' x)) (isapropneg _) (isapropneg _)). 
assert (is3: isweq _ _ map1). apply isweqfibtototal. assumption. 
assert (is4: isweq _ _ map2). apply (isweqfpmap _ _ f  (fun y:Y => neg (paths _ y (f x))) is).
assert (h: forall x0':_, paths _ (map2 (map1 x0')) (maponcomplementsweq _ _ f is x x0')). intro.  simpl. destruct x0'. simpl. apply idpath.
apply (isweqhomot _ _ _ _ h (twooutof3c _ _ _ _ _ is3 is4)).
Defined.






(* Some results on types with an isolated point. *)


Definition isisolated (X:UU0)(x:X):= forall x':X, coprod (paths _ x' x) (paths _ x' x -> empty).




Definition tocomplincoprod (X Y:UU0)(x:X): coprod (complement X x) Y -> complement (coprod X Y) (ii1 _ _ x).
Proof. intros. destruct X0.  split with (ii1 _ _ (pr21 _ _ c)). 

assert (e: neg(paths _ (pr21 _ _ c) x)). apply (pr22 _ _ c). apply (negf _ _ (invmaponpathsincl _ _ (ii1 _ _) (isaninclii1 X Y) _ _) e). 
split with (ii2 _ _ y). apply (negf _ _ (pathsinv0 _ _ _) (negeqii1ii2 X Y x y)). Defined.



Definition fromcomplincoprod (X Y:UU0)(x:X): complement (coprod X Y) (ii1 _ _ x) ->  coprod (complement X x) Y.
Proof. intros. destruct X0.  destruct t. 
assert (ne: neg (paths _ x1 x)). apply (negf _ _ (maponpaths _ _ (ii1 _ _) _ _) x0). apply (ii1 _ _ (complementpair _ _ x1 ne)). apply (ii2 _ _ y). Defined. 


Theorem isweqtocomplincoprod (X Y:UU0)(x:X): isweq _ _ (tocomplincoprod X Y x).
Proof. intros. set (f:= tocomplincoprod X Y x). set (g:= fromcomplincoprod X Y x).
assert (egf:forall nexy:_ , paths _ (g (f nexy)) nexy). intro. destruct nexy. destruct c. simpl. 
assert (e: paths _ (negf (paths X t x) (paths (coprod X Y) (ii1 X Y t) (ii1 X Y x))
              (maponpaths X (coprod X Y) (ii1 X Y) t x)
              (negf (paths (coprod X Y) (ii1 X Y t) (ii1 X Y x))
                 (paths X t x)
                 (invmaponpathsincl X (coprod X Y) 
                    (ii1 X Y) (isaninclii1 X Y) t x) x0)) x0). apply (isapropneg (paths X t x) _ _). 
apply (maponpaths _ _ (fun ee: neg(paths X t x) => ii1 _ _ (complementpair X x t ee)) _ _ e). 
apply idpath.
assert (efg: forall neii1x:_, paths _ (f (g neii1x)) neii1x). intro.  destruct neii1x. destruct t.  simpl. 
assert (e: paths _  (negf (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x)) 
           (paths X x1 x)
           (invmaponpathsincl X (coprod X Y) (ii1 X Y) (isaninclii1 X Y) x1 x)
           (negf (paths X x1 x) (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x))
              (maponpaths X (coprod X Y) (ii1 X Y) x1 x) x0)) x0). apply (isapropneg (paths _ _ _)  _ _).
apply (maponpaths _ _ (fun ee: (neg (paths (coprod X Y) (ii1 X Y x1) (ii1 X Y x))) => (complementpair _ _ (ii1 X Y x1) ee)) _ _ e). 
simpl. 
assert (e: paths _ (negf (paths (coprod X Y) (ii2 X Y y) (ii1 X Y x))
           (paths (coprod X Y) (ii1 X Y x) (ii2 X Y y))
           (pathsinv0 (coprod X Y) (ii2 X Y y) (ii1 X Y x))
           (negeqii1ii2 X Y x y)) x0). apply (isapropneg (paths _ _ _) _ _).
apply (maponpaths  _ _ (fun ee: (neg (paths (coprod X Y) (ii2 X Y y) (ii1 X Y x))) => (complementpair _ _ (ii2 X Y y) ee)) _ _ e). 
apply (gradth _ _ f g egf efg). Defined.





Lemma disjointl1 (X:UU0): isisolated (coprod X unit) (ii2 _ _ tt).
Proof. intros.  unfold isisolated. intros.  destruct x'. apply (ii2 _ _ (negeqii1ii2 _ _ x tt)).  destruct u.  apply (ii1 _ _ (idpath _ _ )). Defined.


Definition tocompltodisjoint (X:UU): X -> complement (coprod X unit) (ii2 _ _ tt) := fun x:_ => complementpair _ _ (ii1 _ _ x) (negeqii1ii2 _ _ x tt).

Definition fromcompltodisjoint (X:UU): complement (coprod X unit) (ii2 _ _ tt) -> X.
Proof. intros. destruct X0.  destruct t. assumption.  destruct u. apply (initmap _ (x (idpath _ (ii2 X _ tt)))). Defined.


Lemma isweqtocompltodisjoint (X:UU): isweq _ _ (tocompltodisjoint X).
Proof. intros. set (ff:= tocompltodisjoint X). set (gg:= fromcompltodisjoint X). 
assert (egf: forall x:X, paths _ (gg (ff x)) x).  intro.  apply idpath.
assert (efg: forall xx:_, paths _ (ff (gg xx)) xx). intro. destruct xx.  destruct t.   simpl. simpl in x. unfold ff. unfold tocompltodisjoint. simpl. assert (ee: paths _  (negeqii1ii2 X unit x0 tt) x).  apply (proofirrelevance _ (isapropneg _) _ _). induction ee. apply idpath. destruct u.  simpl. apply (initmap _ (x (idpath _ _))). apply (gradth _ _ ff gg egf efg).  Defined. 

Corollary isweqfromcompltodisjoint (X:UU): isweq _ _ (fromcompltodisjoint X).
Proof. intros. apply (isweqinvmap _ _ _ (isweqtocompltodisjoint X)). Defined. 

Definition recomplinv (X:UU0)(x:X)(is: isisolated X x): X -> coprod (complement X x) unit:=
fun x':X => match (is x') with
ii1 e => ii2 _ _ tt|
ii2 phi => ii1 _ _ (complementpair _ _ x' phi)
end.



Theorem isweqrecompl (X:UU0)(x:X)(is:isisolated X x): isweq _ _ (recompl X x).
Proof. intros. set (f:= recompl X x). set (g:= recomplinv X x is). unfold recomplinv in g. simpl in g. 
assert (egf: forall u: coprod  (complement X x) unit, paths _ (g (f u)) u). intro. induction u.  unfold f. unfold recompl. induction x0.  unfold g. simpl. induction (is t). induction (x0 x1). 
assert (e: paths _ x0 y). apply (proofirrelevance _ (isapropneg (paths _ t x))). induction e.  apply idpath. 
unfold f. unfold g. simpl. induction y. induction (is x).  apply idpath. induction (y (idpath _ x)).

assert (efg: forall x':X, paths _ (f (g x')) x'). intro.   induction (is x').   induction x0. unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x').  simpl. apply idpath. induction (y (idpath _ x')).  unfold f. unfold g. simpl. unfold recompl. simpl.  induction (is x').  induction (y x0). simpl. apply idpath.
apply (gradth _ _ f g egf efg). Defined.


Lemma isolatedtoisolated (X:UU0)(Y:UU0)(f:X -> Y)(is1:isweq _ _ f)(x:X)(is2: isisolated _ x): isisolated _ (f x).
Proof.  intros. unfold isisolated. intro. rename x' into y.  set (g:=invmap _ _ f is1). set (x':= g y). induction (is2 x').  apply (ii1 _ _ (pathsinv0 _ _ _ (pathsweq1' _ _ f is1 x y (pathsinv0 _ _ _ x0)))). 
assert (phi: paths _ y (f x)  -> empty). 
assert (psi: (paths _ (g y) x -> empty) -> (paths _ y (f x) -> empty)). intro. intro.  apply (X0  (pathsinv0 _ _ _ (pathsweq1 _ _ f is1 x y (pathsinv0 _ _ _ X1)))). apply (psi y0). apply (ii2 _ _ phi). Defined.

















(* Finite sets. I. *)






Definition isofnel (n:nat)(X:UU0):UU0 := dneg (weq (stn n) X). 

Lemma stnsnegl1 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ X lp). Defined.

Lemma stnsnegl2 (n:nat): neg (weq (stn O) (stn (S n))).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply (ii2 _ _ tt). intro.  apply (pr21 _ _ (weqinv _ _ X) lp). Defined.

Lemma stnsposl0 (n:nat): weq (stn n) (complement (stn (S n)) (ii2 _ _ tt)).
Proof. intros. split with (tocompltodisjoint (stn n)). apply isweqtocompltodisjoint. Defined.

Lemma stnsposl1 (n:nat)(x: stn (S n)): weq (stn n) (complement (stn (S n)) x).
Proof. intro. induction n. intros. simpl in x.  destruct x.  apply (initmap _ e). simpl. destruct u. apply (stnsposl0 O). intro. simpl in x. destruct x. set  (g:=tocomplincoprod _ unit c).  set (f:= coprodf _ _ _ _ (pr21 _ _ (IHn c)) (fun t:unit => t)).  split with (fun x:_ => g (f x)). 
assert (is1:isweq _ _ f). apply (isweqcoprodf _ _ _ _ _ _ (pr22 _ _ (IHn c)) (idisweq unit)). 
assert (is2: isweq _ _ g). apply (isweqtocomplincoprod _ unit c). 
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
 intro. induction n'. intros. set (int:= isdeceqnat (S n) O).  destruct int.  assumption. apply (initmap _ (stnsnegl1 n X)).  intro. 
set (e:= IHn n' (stnsposl2 n n' X)). apply (maponpaths _ _ S _ _ e). Defined. 


Definition isfinite (X:UU0):UU0:= total2 nat (fun n:nat => isofnel n X).

Theorem isapropisfinite (X:UU0): isaprop (isfinite X).
Proof. intros. assert (is1: (isfinite X) -> (iscontr (isfinite X))).  intro. unfold iscontr. split with X0.  intro. destruct X0.  destruct t.
assert (c1: coprod (paths _ t t0) (neg (paths _ t t0))). apply isdeceqnat. destruct c1.  apply (invmaponpathsincl (isfinite X) nat (pr21 _ _) (isofhlevelfpr21 (S O) _ _  (fun n:nat => isapropdneg (weq (stn n) X))) (tpair nat (fun n : nat => isofnel n X) t x0) (tpair nat (fun n : nat => isofnel n X) t0 x) p).  
assert (is1: dneg (dirprod (weq (stn t0) X) (weq (stn t) X))). apply (dneganddnegimpldneg _ _ x x0). 
assert (is2: dneg (weq (stn t0) (stn t))). apply (dnegf _ _ (fun fg: dirprod (weq (stn t0) X) (weq (stn t) X) => weqcomp _ _ _ (pr21 _ _ fg) (weqinv _ _ (pr22 _ _ fg))) is1).   apply (initmap _ (dnegf _ _ (fun ee:_ => pathsinv0 _ _ _ (stnsweqtoeq t0 t ee)) is2 n)). apply (iscontraprop1inv _ is1).  Defined.






Definition fsets := u2.total2 UU0 (fun X:UU0 => isfinite X).

Definition fcurry (X:fsets): UU0 := u2.pr21 _ _ X.

Definition numofel (X:fsets): nat:= pr21 _ _ (u2.pr22 _ _ X). 






(* Some other constructions *)

Lemma ifcontrthenunit: forall T:UU0, (iscontr T) -> u2.paths _ T unit. 
Proof. intros.  apply isweqcontrtounit in X. apply weqtopaths in X. assumption. Defined. 





















(* End of the file u01.v *)






