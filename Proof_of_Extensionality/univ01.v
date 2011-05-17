
(** This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun. 

This proof requires one to use some of the general definitions and results of the univalent approach both for the universe for which funextfun is being proved and for the universe which is one level higher.  Moreover, the proof of dependent extensionality (Theorem funcontr) which is given in the file u012.v requires funextfun for the universe one level higher than the one for which funcontr is being proved. 

Since Coq8.3 does not have a support for universe polymorphic definitions we have to explicitly repeat some of the definitions and constructions twice and some three times. This is done by creating three identical files with basic definitions and constructions u0.v u1.v and u2.v and two almost identical files u01.v and u12.v with the proofs of funextfun. The only difference between u01.v and u12.v is that the later is obtained from the former by the replacement of all occurences of [u01.] by [u12.], all occurences of [u1.] by [u2.], all occurences of [u0.] by [u1.] and the removal of this comment.  

*)


(** * Preamble. *)

(** ** Imports. *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Require Export u1.
Require Export u0.


(** Note: since the file u0.v is imported last, the current agreement in Coq implies that  [paths] is the same as [u0.paths], [weq] is the same as [u0.weq] etc. while to access identifiers from u1.v one has to write explicitly [u1.paths] etc. *)



(** * The hierarchy of universes. *)


(** The following definitions establish the hierarchy of universes such that UU0=u0.UU, UU1=u1.UU,  UU0:UU1 and UU0 is a subtype of UU1**)

Notation UU0:=u0.UU.
Notation UU1:=u1.UU.

Definition j01:UU0 -> UU1:= fun T:UU0 => T. 
Definition j11:UU1 -> UU1:= fun T:UU1 => T.

Definition UU0inUU1:= j11 UU0.


(** Coercion related settings. **)

Definition totype0:= (fun X:UU0 => X): UU0 -> Type.
Coercion totype0: UU0 >-> Sortclass.

Definition totype1:= (fun X:UU1 => X): UU1 -> Type.
Coercion totype1: UU1 >-> Sortclass.

(** Some connections between u0 and u1 definitions. *)

Theorem u1pathstou0paths : forall (X:UU0)(x x':X), u1.paths _ x x' -> paths _ x x'.
Proof.  intros.  destruct X0. apply idpath. Defined.

Theorem u0pathstou1paths: forall (X:UU0)(x x':X), paths _ x x' -> u1.paths _ x x'.
Proof. intros. destruct X0. apply u1.idpath. Defined. 

Theorem iswequ1pathstou0paths (X:UU0)(x x':X): u1.isweq _ _ (u1pathstou0paths _ x x').
Proof. intros. set (f:=u1pathstou0paths _ x x'). set (g:= u0pathstou1paths _ x x').
assert (egf: forall a:_,  u1.paths _ (g (f a)) a). intros. destruct a. simpl.  apply u1.idpath. 
assert (efg: forall a:_, u1.paths _ (f (g a)) a). intros. destruct a. simpl. apply u1.idpath.
apply (u1.gradth _ _ _ _ egf efg). Defined. 

Coercion u1pathstou0paths: u1.paths >-> paths.

Theorem u1iscontrtou0iscontr (X:UU0): u1.iscontr X -> iscontr X.
Proof. intros. split with (u1.pr21 _ _ X0). 
intro.  set (s:=u1.contrl2 X X0 t (u1.pr21 X (fun cntr : X => forall t0 : X, u1.paths X t0 cntr) X0)). apply (u1pathstou0paths X t _ s). Defined.

Coercion  u1iscontrtou0iscontr: u1.iscontr >-> iscontr.


Theorem u0iscontrtou1iscontr (X:UU0): iscontr X -> u1.iscontr X.
Proof. intros. split with (pr21 _ _ X0). 
 intro. apply (u0pathstou1paths _ t _). apply (contrl2 X X0 _ _ ). Defined.

Coercion u0iscontrtou1iscontr: iscontr  >-> u1.iscontr.
 
Theorem u1isofhleveltou0isofhlevel (n:nat)(X:UU0): u1.isofhlevel n X -> u0.isofhlevel n X.
Proof. intro. induction n. intro.  apply u1iscontrtou0iscontr. intro. simpl. intro. intros. set (s:= X0 x x'). 
set (s1:=u1.isofhlevelweqf n _ _  (u1pathstou0paths X x x') (iswequ1pathstou0paths X x x') s). apply (IHn _ s1).
Defined.

Coercion  u1isofhleveltou0isofhlevel: u1.isofhlevel >-> isofhlevel.


Theorem u0isofhleveltou1isofhlevel  (n:nat)(X:UU0): isofhlevel n X -> u1.isofhlevel n X.
Proof. intro. induction n.  intro.  apply u0iscontrtou1iscontr. intros. simpl. intros.  
assert (s:u1.isofhlevel n (paths _ x x')). apply (IHn _ (X0 x x')). apply (u1.isofhlevelweqb n _ _ _ (iswequ1pathstou0paths _ x x') s). Defined.  

Coercion u0isofhleveltou1isofhlevel: isofhlevel >-> u1.isofhlevel.






(** * Univalence and extensionality. *)

(** ** Univalence axiom. *)


Definition eqweqmap (T1:UU0) (T2:UU0) : (u1.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU0, forall T2:UU0, u1.isweq (u1.paths Type T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f): u1.paths _ T1 T2 := u1.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).


Definition weqpathsweq (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq _ _ f):u1.paths _ (eqweqmap _ _ (weqtopaths _ _ f is)) (weqpair _ _ f is) := u1.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) (weqpair _ _ f is).

(** Conjecture: univalenceaxiom is equivalent to two axioms 

[Axiom weqtopaths0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f): paths1 _ T1 T2.]

[Axiom weqpathsweq0 (T1:UU0)(T2:UU0)(f:T1 -> T2)(is:isweq0 _ _ f):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ f is)) (weqpair0 _ _ f is).]

*)


(** ** Transport theorem. 

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


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
apply (isweqhomot _ _ (u1.transportb UU0 P X X' (weqtopaths X X' u is)) (fun p' : P X' => R X X' u is p') ee is1).  Defined. 



    

(** Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)




Theorem isweqcompwithweq (X:UU0)(X':UU0)(u:X->X')(is:isweq _ _ u)(Y:UU0): isweq _ _ (fun f:X'->Y => (fun x:X => f (u x))).
Proof. intros. 
set (P:= fun X0:UU0 => (X0 -> Y)). 
set (R:= fun X0:UU0 => (fun X0':UU0 => (fun u0:X0 -> X0' => (fun is0:isweq _ _ u0 => (fun  f:P X0'  => (fun x:X0 => f (u0 x))))))). 
set (r:= fun X0:UU0 => (fun f:X0 -> Y => pathsinv0 _ _ _ (etacor X0 Y f))).
apply (isweqweqtransportb P R r X X' u is). Defined.




(** ** Proof of the functional extensionality for functions *)





Lemma eqcor0 (X:UU0)(X':UU0)(u:X->X')(is:isweq _ _ u)(Y:UU0)(f1:X'->Y)(f2:X'->Y):  (paths _ (fun x:X => f1 (u x))  (fun x:X => f2 (u x))) -> paths _ f1 f2. 
Proof. intros. apply (pathsweq2 _ _ (fun f:X'->Y => (fun x:X => f (u x))) (isweqcompwithweq _ _ u is Y) f1 f2). assumption.  Defined. 


Lemma apathpr1topr2 (T:UU0) : paths _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z)).
Proof. intro. apply (eqcor0 _ _  (deltap T) (isweqdeltap T) _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z))  (idpath _ (fun t:T => t))). Defined.     


Theorem funextfun (X:UU0)(Y:UU0)(f1:X->Y)(f2:X->Y)(e: forall x:X, paths _ (f1 x) (f2 x)): paths _ f1 f2.
Proof. intros. set (f:= (fun x:X => pathsspacetriple Y (f1 x) (f2 x) (e x))).  set (g1:= (fun z:pathsspace Y => pr21 _ _ z)). set (g2:= fun z: pathsspace Y => pr21 _ _ (pr22 _ _ z)). assert (e': paths _ g1 g2). apply (apathpr1topr2 Y). assert (ee:paths _ (fun x:X => f1 x) (fun x:X => f2 x)). apply (maponpaths2b _ _ _ f g1 g2 e').  apply etacoronpaths.  assumption. Defined. 





(** * Types of properties and sets *)




Definition hProp0:= (u1.total2 UU0 (fun X:UU0 => u0.isaprop X)).
Definition hProp0pair:= u1.tpair  UU0 (fun X:UU0 => u0.isaprop X).
Definition hPropcarrier0 := u1.pr21  UU0 (fun X:UU0 => u0.isaprop X): hProp0 -> UU0.
Coercion hPropcarrier0: hProp0 >-> UU0.


Definition hSet0:= u1.total2 UU0 (fun X:UU0 => u0.isaset X).
Definition hSet0pair := u1.tpair UU0 (fun X:UU0 => u0.isaset X).
Definition hSetcarrier0:= u1.pr21 UU0 (fun X:UU0 => u0.isaset X) : hSet0 -> UU0.
Coercion hSetcarrier0: hSet0 >-> UU0.


(** * Inhabited construction **)

Definition isinhcomb0 (X:UU0) := forall P:hProp0, ((X->P)->P).



(** * Relations **)


Definition hrel0 (X:UU0) := forall x1 x2 : X, hProp0.

Definition trans0 (X:UU0) (rel: hrel0 X):= forall x1 x2 x3 : X, forall (f1: rel  x1 x2) (f2: rel x2 x3), rel x1 x3.

Definition refl0 (X:UU0)(rel:hrel0 X) := forall x:X, rel x x.

Definition symm0 (X:UU0)(rel:hrel0 X):= forall x1 x2 : X, rel x1 x2 -> rel x2 x1.



(** * Types of subsets **)



Definition hsubtypes0 (X:UU0) := X -> hProp0.
Definition hsubtypecarrier0 (X:UU0)(A:hsubtypes0 X):= u0.total2 X (fun x:X => A x).
Coercion hsubtypecarrier0: hsubtypes0 >-> UU0.

(** * Some types of level 1 and 2 in UU1 **)

Theorem isapropisinh (X:UU0): u1.isaprop (isinh X).
Proof. intro. unfold isinh. 
assert (s1:forall (P:UU0)(is: isaprop P), isaprop ((X->P)->P)). intros. unfold isaprop. apply impredfun. assumption. 
assert (s2: forall (P:UU0), isaprop (isaprop P -> (X->P) ->P)). intro. apply impredtech1. apply (s1 P). 
assert (s3: forall (P:UU0), u1.isaprop (isaprop P -> (X-> P) -> P)). intro. apply (u0isofhleveltou1isofhlevel 1 _ (s2 P)). apply u1.impred. assumption.  Defined. 




(* End of the file u01.v *)






