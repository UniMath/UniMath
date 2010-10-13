Require Export u2.
Require Export u1.



(* The following definitions establish the hierarchy of universes such that

UU0=u1.UU
UU1=u2.UU

UU0:UU1 and UU0 is a subtype of UU1 *)


Definition j01:UU -> u2.UU:= fun T:UU => T. 
Definition j11:u2.UU -> u2.UU:=fun T:u2.UU => T.

Definition UU0:=j11 UU.
Definition UU1:=u2.UU.


(* Note: by the current agreement in Coq, the names introduced in u1, as the last module to be imported, "shadow" the names introduced in u2 so that, for example, paths is the same as u1.paths and UU is the same as u1.UU *)







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
apply (isweqhom _ _ (u2.transportb UU0 P X X' (weqtopaths X X' u is)) (fun p' : P X' => R X X' u is p') ee is1).  Defined. 



    

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


(* More results on h-levels. *)

Lemma ifcontrthenunit: forall T:UU0, (iscontr T) -> u2.paths _ T unit. 
Proof. intros.  apply isweqcontrtounit in X. apply weqtopaths in X. assumption. Defined. 


Lemma iscontrtounit (T:UU0) :iscontr (T -> unit).
Proof. intros. set (cntr:= (fun t:T => tt)). split with cntr. intros. assert (e: forall f1: T -> unit, forall t:T,  paths _ (f1 t) tt). intros. induction (f1 t0). apply idpath. apply (funextfun T unit t cntr (e t)). Defined. 



Theorem isapropneg (X:UU0): isaprop (X -> empty).
Proof. intro. unfold isaprop. unfold isofhlevel.  
assert (is1:forall (f g: X -> empty), forall x:X, paths _ (f x) (g x)). intros.  apply initmap. apply (f x). 
assert (is2: forall (f g:X -> empty), paths _ f g). intros.  apply (funextfun _ _ f g (is1 f g)). apply (isaprop2 _ is2). Defined.


Theorem isapropxornotx (X:UU): (isaprop X) -> (isaprop (coprod X (X-> empty))).
Proof. intros. 
assert (forall (x x': X), paths _ x x'). apply (isaprop2' _ X0).  
assert (forall (x x': coprod X (X -> empty)), paths _ x x'). intros.  
induction x. induction t. induction x'.  induction t. apply (maponpaths _ _ (fun x:X => ii1 _ _ x) _ _ (X1 x x0)).    
apply (initmap _ (x0 x)). induction x'. induction t.  apply (initmap _ (x x0)). 
assert (e: paths _ x x0). apply (isaprop2' _ (isapropneg X) x x0). apply (maponpaths _ _ (fun f: X -> empty => ii2 _ _ f) _ _ e).
apply (isaprop2 _ X2).  Defined. 





(* End of the file u12.v *)





