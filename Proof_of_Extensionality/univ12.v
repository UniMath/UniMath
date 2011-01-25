Add Rec LoadPath "../Main_Library/".


(** This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun. 

This proof requires one to use some of the general definitions and results of the univalent approach both for the universe for which funextfun is being proved and for the universe which is one level higher.  Moreover, the proof of dependent extensionality (Theorem funcontr) which is given in the file u012.v requires funextfun for the universe one level higher than the one for which funcontr is being proved. 

Since Coq8.3 does not have a support for universe polymorphic definitions we have to explicitly repeat some of the definitions and constructions twice and some three times. This is done by creating three identical files with basic definitions and constructions u0.v u1.v and u2.v and two almost identical files u01.v and u12.v with the proofs of funextfun. The only difference between u01.v and u12.v is that the later is obtained from the former by the replacement of all occurences of [u01.] by [u12.], all occurences of [u1.] by [u2.], all occurences of [u0.] by [u1.] and the removal of this comment.  
*)


(** * Preamble. *)

(** ** Imports. *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Require Export u2.
Require Export u1.



(** Note: since the file u1.v is imported last, the current agreement in Coq implies that  [paths] is the same as [u1.paths], [weq] is the same as [u1.weq] etc. while to access identifiers from u2.v one has to write explicitly [u2.paths] etc. *)



(** * The hierarchy of universes. *)


(** The following definitions establish the hierarchy of universes such that UU1=u1.UU, UU2=u2.UU,  UU1:UU2 and UU1 is a subtype of UU2**)

Notation UU1:=u1.UU.
Notation UU2:=u2.UU.

Definition j01:UU1 -> UU2:= fun T:UU1 => T. 
Definition j11:UU2 -> UU2:= fun T:UU2 => T.

Definition UU1inUU2:= j11 UU1.

Identity Coercion totype1: UU1 >-> Sortclass.
Identity Coercion totype2: UU2 >-> Sortclass.

(** Some connections between u1 and u2 definitions. *)

Theorem u2pathstou1paths : forall (X:UU1)(x x':X), u2.paths _ x x' -> paths _ x x'.
Proof.  intros.  destruct X0. apply idpath. Defined.

Theorem u1pathstou2paths: forall (X:UU1)(x x':X), paths _ x x' -> u2.paths _ x x'.
Proof. intros. destruct X0. apply u2.idpath. Defined. 

Theorem iswequ2pathstou1paths (X:UU1)(x x':X): u2.isweq _ _ (u2pathstou1paths _ x x').
Proof. intros. set (f:=u2pathstou1paths _ x x'). set (g:= u1pathstou2paths _ x x').
assert (egf: forall a:_,  u2.paths _ (g (f a)) a). intros. destruct a. simpl.  apply u2.idpath. 
assert (efg: forall a:_, u2.paths _ (f (g a)) a). intros. destruct a. simpl. apply u2.idpath.
apply (u2.gradth _ _ _ _ egf efg). Defined. 

Coercion u2pathstou1paths: u2.paths >-> paths.

Theorem u2iscontrtou1iscontr (X:UU1): u2.iscontr X -> iscontr X.
Proof. intros. split with (u2.pr21 _ _ X0). 
intro.  set (s:=u2.contrl2 X X0 t (u2.pr21 X (fun cntr : X => forall t0 : X, u2.paths X t0 cntr) X0)). apply (u2pathstou1paths X t _ s). Defined.

Coercion  u2iscontrtou1iscontr: u2.iscontr >-> iscontr.


Theorem u1iscontrtou2iscontr (X:UU1): iscontr X -> u2.iscontr X.
Proof. intros. split with (pr21 _ _ X0). 
 intro. apply (u1pathstou2paths _ t _). apply (contrl2 X X0 _ _ ). Defined.

Coercion u1iscontrtou2iscontr: iscontr  >-> u2.iscontr.
 
Theorem u2isofhleveltou1isofhlevel (n:nat)(X:UU1): u2.isofhlevel n X -> u1.isofhlevel n X.
Proof. intro. induction n. intro.  apply u2iscontrtou1iscontr. intro. simpl. intro. intros. set (s:= X0 x x'). 
set (s1:=u2.isofhlevelweqf n _ _  (u2pathstou1paths X x x') (iswequ2pathstou1paths X x x') s). apply (IHn _ s1).
Defined.

Coercion  u2isofhleveltou1isofhlevel: u2.isofhlevel >-> isofhlevel.


Theorem u1isofhleveltou2isofhlevel  (n:nat)(X:UU1): isofhlevel n X -> u2.isofhlevel n X.
Proof. intro. induction n.  intro.  apply u1iscontrtou2iscontr. intros. simpl. intros.  
assert (s:u2.isofhlevel n (paths _ x x')). apply (IHn _ (X0 x x')). apply (u2.isofhlevelweqb n _ _ _ (iswequ2pathstou1paths _ x x') s). Defined.  

Coercion u1isofhleveltou2isofhlevel: isofhlevel >-> u2.isofhlevel.






(** * Univalence and extensionality. *)

(** ** Univalence axiom. *)


Definition eqweqmap (T1:UU1) (T2:UU1) : (u2.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU1, forall T2:UU1, u2.isweq (u2.paths Type T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU1)(T2:UU1)(w: weq T1 T2) : u2.paths _ T1 T2 := u2.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.


Definition weqpathsweq (T1:UU1)(T2:UU1)(w: weq T1 T2):u2.paths _ (eqweqmap _ _ (weqtopaths _ _ w)) w := u2.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.

(** Conjecture: univalenceaxiom is equivalent to two axioms 

[Axiom weqtopaths0 (T1:UU1)(T2:UU1)(w: weq T1 T2): paths1 _ T1 T2.]

[Axiom weqpathsweq0 (T1:UU1)(T2:UU1)(w: weq T1 T2):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ w)) (weqpair0 _ _ w).]

 *)

Axiom weqtopaths0: forall (T1:UU1)(T2:UU1)(w:weq T1 T2), u2.paths _ T1 T2.

Axiom weqpathsweq0: forall (T1:UU1)(T2:UU1)(w:weq T1 T2), u2.paths _ (eqweqmap _ _ (weqtopaths0 _ _ w)) w.

Theorem univfromtwoaxioms: forall T1:UU1, forall T2:UU1, u2.isweq (u2.paths Type T1 T2) (weq T1 T2) (eqweqmap T1 T2).
Proof. intros. set (P1:= fun XY: u2.dirprod UU1 UU1 => (match XY with u2.tpair X Y => u2.paths _ X Y end)). set (P2:= fun XY: u2.dirprod UU1 UU1 => match XY with u2.tpair X Y => weq X Y end). set (Z1:= u2.total2 _ P1). set (Z2:= u2.total2 _ P2). set (f:= (u2.totalfun _ _ _ (fun XY:u2.dirprod UU1 UU1 => (match XY with u2.tpair X Y => eqweqmap X Y end))): Z1 -> Z2). set (g:=  (u2.totalfun _ _ _ (fun XY:u2.dirprod UU1 UU1 => (match XY with u2.tpair X Y => weqtopaths0 X Y end))): Z2 -> Z1). set (s1:= (fun X Y :UU1 => fun w: weq X Y => u2.tpair _ P2 (u2.dirprodpair _ _ X Y) w)). set (efg:= (fun a:_ => match a as a' return (u2.paths _ (f (g a')) a') with u2.tpair (u2.tpair X Y) w => (u2.maponpaths _ _ (s1 X Y) _ _ (weqpathsweq0 X Y w)) end)). 

set (h:= fun a1:Z1 => (u2.pr21 _ _ (u2.pr21 _ _ a1))).
assert (egf0: forall a1:Z1, u2.paths (u2.dirprod UU1 UU1) (u2.pr21 _ _ (g (f a1))) (u2.pr21 _ _ a1)). intro. apply u2.idpath.  
assert (egf1: forall a1 a1':Z1, u2.paths _ (u2.pr21 _ _ a1') (u2.pr21 _ _ a1) -> u2.paths _ a1' a1). intros.  set (X':= u2.maponpaths _ _ (u2.pr21 _ _ ) _ _ X). 
assert (is: u2.isweq _ _ h).  apply (u2.isweqpr21pr21). apply (u2.pathsweq2 _ _ h is _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:=u2.gradth _ _ _ _ egf efg). 
apply (u2.isweqtotaltofib _ P1 P2  (fun XY:u2.dirprod UU1 UU1 => (match XY with u2.tpair X Y => eqweqmap X Y end)) is2 (u2.dirprodpair _ _ T1 T2)). Defined. 


(** We now want to show that the pair [weqtopaths0] and [weatopathsweq0] is well defined up to a canonical equality. **)






(** ** Transport theorem. 

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 (X:UU2)(P:X -> UU1)(x:X)(x':X)(e:u2.paths _ x x'): isweq _ _ (u2.transportf X P x x' e).
Proof. intros. induction e.  apply idisweq. Defined.

Lemma isweqtransportb10 (X:UU2)(P:X -> UU1)(x:X)(x':X)(e:u2.paths _ x x'): isweq _ _ (u2.transportb X P x x' e).
Proof. intros. apply (isweqtransportf10 _ _ _ _ (u2.pathsinv0 _ _ _ e)). Defined. 



Lemma l1  (X0:UU1)(X0':UU1)(ee: u2.paths _ X0 X0')(P:UU1 -> UU1)(pp': P X0')(R: forall X:UU1, forall X':UU1, forall w: weq X X', P X' -> P X)(r: forall X:UU1, forall p:P X, paths _ (R X X (idweq X) p) p):paths _ (R X0 X0' (eqweqmap _ _ ee) pp') (u2.transportb UU1 P X0 X0' ee pp').
Proof. intro. intro. intro. intro. intro. induction ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb  (P:UU1 -> UU1)(R: forall (X X':UU1) (w: weq X X'), P X' -> P X)(r: forall X:UU1, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU1) (w: weq X X') (p':P X'), paths _ (R X X' w p') (u2.transportb UU1  P X X' (weqtopaths _ _ w) p').  
Proof. intros. set (uv:=weqtopaths _ _ w).   set (v:=eqweqmap _ _ uv). 

assert (e:u2.paths _ v w). unfold weqtopaths in uv.  apply (u2.weqfg  (u2.paths UU1 X X') (weq X X')  (eqweqmap X X') (univalenceaxiom X X') w).

assert (ee:u2.paths _ (R X X' v p') (R X X' w p')). set (R':= fun vis:weq X X' => R X X' vis p'). assert (ee':u2.paths _ (R' v) (R' w)). apply (u2.maponpaths (weq X X') (P X) R' _ _ e). assumption.

induction ee. apply l1. assumption. Defined.



Corollary isweqweqtransportb (P:UU1 -> UU1)(R: forall (X X':UU1) (w: weq X X'), P X' -> P X)(r: forall X:UU1, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU1)(w: weq X X'), isweq _ _ (fun p': P X' => R X X' w p').
Proof. intros. assert (e:forall p':P X', paths _ (R X X' w p') (u2.transportb UU1 P X X' (weqtopaths _ _ w) p')). apply weqtransportb. assumption. assert (ee :forall p':P X', paths _  (u2.transportb UU1 P X X' (weqtopaths _ _ w) p') (R X X' w p')). intro.  apply (pathsinv0 _ _ _ (e p')). clear e. 

assert (is1:isweq _ _ (u2.transportb UU1 P X X' (weqtopaths _ _ w))). apply isweqtransportb10.  
apply (isweqhomot _ _ (u2.transportb UU1 P X X' (weqtopaths X X' w)) (fun p' : P X' => R X X' w p') ee is1).  Defined. 



    

(** Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)




Theorem isweqcompwithweq (X:UU1)(X':UU1)(u:X->X')(is:isweq _ _ u)(Y:UU1): isweq _ _ (fun f:X'->Y => (fun x:X => f (u x))).
Proof. intros. 
set (P:= fun X0:UU1 => (X0 -> Y)). 
set (R:= fun X0:UU1 => (fun X0':UU1 => (fun u1:X0 -> X0' => (fun is0:isweq _ _ u1 => (fun  f:P X0'  => (fun x:X0 => f (u1 x))))))). 
set (r:= fun X0:UU1 => (fun f:X0 -> Y => pathsinv0 _ _ _ (etacor X0 Y f))).
apply (isweqweqtransportb P R r X X' u is). Defined.




(** ** Proof of the functional extensionality for functions *)





Lemma eqcor0 (X:UU1)(X':UU1)(u:X->X')(is:isweq _ _ u)(Y:UU1)(f1:X'->Y)(f2:X'->Y):  (paths _ (fun x:X => f1 (u x))  (fun x:X => f2 (u x))) -> paths _ f1 f2. 
Proof. intros. apply (pathsweq2 _ _ (fun f:X'->Y => (fun x:X => f (u x))) (isweqcompwithweq _ _ u is Y) f1 f2). assumption.  Defined. 


Lemma apathpr1topr2 (T:UU1) : paths _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z)).
Proof. intro. apply (eqcor0 _ _  (deltap T) (isweqdeltap T) _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z))  (idpath _ (fun t:T => t))). Defined.     


Theorem funextfun (X:UU1)(Y:UU1)(f1:X->Y)(f2:X->Y)(e: forall x:X, paths _ (f1 x) (f2 x)): paths _ f1 f2.
Proof. intros. set (f:= (fun x:X => pathsspacetriple Y (f1 x) (f2 x) (e x))).  set (g1:= (fun z:pathsspace Y => pr21 _ _ z)). set (g2:= fun z: pathsspace Y => pr21 _ _ (pr22 _ _ z)). assert (e': paths _ g1 g2). apply (apathpr1topr2 Y). assert (ee:paths _ (fun x:X => f1 x) (fun x:X => f2 x)). apply (maponpaths2b _ _ _ f g1 g2 e').  apply etacoronpaths.  assumption. Defined. 



(* End of the file u12.v *)






