Add Rec LoadPath "../Main_Library/".


(** This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun. 

This proof requires one to use some of the general definitions and results of the univalent approach both for the universe for which funextfun is being proved and for the universe which is one level higher.  

Since Coq8.3 does not have a support for explicit universe polymorphic definitions we have to explicitly repeat some of the definitions and constructions twice and some three times. This is done by creating three identical files with basic definitions and constructions u0.v u1.v and u2.v and two almost identical files univ01.v and univ12.v with the proofs of funextfun. The only difference between univ01.v and univ12.v is that the later is obtained from the former by the replacement of all occurences of [univ01.] by [univ12.], all occurences of [u1.] by [u2.] and all occurences of [u0.] by [u1.].

The new proof of functional extensionality for the dependent functions from the functional extensionality of usual functions given in u?.v makes itunnessesary to use three universe levels to deduce extensionality for dependent functions from the univalence axiom. 
   
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

Identity Coercion totype1: UU0 >-> Sortclass.
Identity Coercion totype2: UU1 >-> Sortclass.





(** * Univalence and extensionality. *)

(** ** Univalence axiom. *)


Definition eqweqmap (T1:UU0) (T2:UU0) : (u1.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU0, forall T2:UU0, u1.isweq (u1.paths _ T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU0)(T2:UU0)(w: weq T1 T2) : u1.paths _ T1 T2 := u1.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.


Definition weqpathsweq (T1:UU0)(T2:UU0)(w: weq T1 T2):u1.paths _ (eqweqmap _ _ (weqtopaths _ _ w)) w := u1.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.

(** Conjecture: univalenceaxiom is equivalent to two axioms 

[Axiom weqtopaths0 (T1:UU0)(T2:UU0)(w: weq T1 T2): paths1 _ T1 T2.]

[Axiom weqpathsweq0 (T1:UU0)(T2:UU0)(w: weq T1 T2):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ w)) (weqpair0 _ _ w).]

 *)

Axiom weqtopaths0: forall (T1:UU0)(T2:UU0)(w:weq T1 T2), u1.paths _ T1 T2.

Axiom weqpathsweq0: forall (T1:UU0)(T2:UU0)(w:weq T1 T2), u1.paths _ (eqweqmap _ _ (weqtopaths0 _ _ w)) w.

Theorem univfromtwoaxioms: forall T1:UU0, forall T2:UU0, u1.isweq (u1.paths _ T1 T2) (weq T1 T2) (eqweqmap T1 T2).
Proof. intros. set (P1:= fun XY: u1.dirprod UU0 UU0 => (match XY with u1.tpair X Y => u1.paths _ X Y end)). set (P2:= fun XY: u1.dirprod UU0 UU0 => match XY with u1.tpair X Y => weq X Y end). set (Z1:= u1.total2 _ P1). set (Z2:= u1.total2 _ P2). set (f:= (u1.totalfun _ _ _ (fun XY:u1.dirprod UU0 UU0 => (match XY with u1.tpair X Y => eqweqmap X Y end))): Z1 -> Z2). set (g:=  (u1.totalfun _ _ _ (fun XY:u1.dirprod UU0 UU0 => (match XY with u1.tpair X Y => weqtopaths0 X Y end))): Z2 -> Z1). set (s1:= (fun X Y :UU0 => fun w: weq X Y => u1.tpair _ P2 (u1.dirprodpair _ _ X Y) w)). set (efg:= (fun a:_ => match a as a' return (u1.paths _ (f (g a')) a') with u1.tpair (u1.tpair X Y) w => (u1.maponpaths _ _ (s1 X Y) _ _ (weqpathsweq0 X Y w)) end)). 

set (h:= fun a1:Z1 => (u1.pr21 _ _ (u1.pr21 _ _ a1))).
assert (egf0: forall a1:Z1, u1.paths (u1.dirprod UU0 UU0) (u1.pr21 _ _ (g (f a1))) (u1.pr21 _ _ a1)). intro. apply u1.idpath.  
assert (egf1: forall a1 a1':Z1, u1.paths _ (u1.pr21 _ _ a1') (u1.pr21 _ _ a1) -> u1.paths _ a1' a1). intros.  set (X':= u1.maponpaths _ _ (u1.pr21 _ _ ) _ _ X). 
assert (is: u1.isweq _ _ h).  apply (u1.isweqpr21pr21). apply (u1.pathsweq2 _ _ h is _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:=u1.gradth _ _ _ _ egf efg). 
apply (u1.isweqtotaltofib _ P1 P2  (fun XY:u1.dirprod UU0 UU0 => (match XY with u1.tpair X Y => eqweqmap X Y end)) is2 (u1.dirprodpair _ _ T1 T2)). Defined. 


(** Conjecture: the pair [weqtopaths0] and [weatopathsweq0] is well defined up to a canonical equality. **)






(** ** Transport theorem. 

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u1.paths _ x x'): isweq _ _ (u1.transportf X P x x' e).
Proof. intros. induction e.  apply idisweq. Defined.

Lemma isweqtransportb10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:u1.paths _ x x'): isweq _ _ (u1.transportb X P x x' e).
Proof. intros. apply (isweqtransportf10 _ _ _ _ (u1.pathsinv0 _ _ _ e)). Defined. 



Lemma l1  (X0:UU0)(X0':UU0)(ee: u1.paths _ X0 X0')(P:UU0 -> UU0)(pp': P X0')(R: forall X:UU0, forall X':UU0, forall w: weq X X', P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p):paths _ (R X0 X0' (eqweqmap _ _ ee) pp') (u1.transportb UU0 P X0 X0' ee pp').
Proof. intro. intro. intro. intro. intro. induction ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb  (P:UU0 -> UU0)(R: forall (X X':UU0) (w: weq X X'), P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU0) (w: weq X X') (p':P X'), paths _ (R X X' w p') (u1.transportb UU0  P X X' (weqtopaths _ _ w) p').  
Proof. intros. set (uv:=weqtopaths _ _ w).   set (v:=eqweqmap _ _ uv). 

assert (e:u1.paths _ v w). unfold weqtopaths in uv.  apply (u1.weqfg  (u1.paths UU0 X X') (weq X X')  (eqweqmap X X') (univalenceaxiom X X') w).

assert (ee:u1.paths _ (R X X' v p') (R X X' w p')). set (R':= fun vis:weq X X' => R X X' vis p'). assert (ee':u1.paths _ (R' v) (R' w)). apply (u1.maponpaths (weq X X') (P X) R' _ _ e). assumption.

induction ee. apply l1. assumption. Defined.



Corollary isweqweqtransportb (P:UU0 -> UU0)(R: forall (X X':UU0) (w: weq X X'), P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU0)(w: weq X X'), isweq _ _ (fun p': P X' => R X X' w p').
Proof. intros. assert (e:forall p':P X', paths _ (R X X' w p') (u1.transportb UU0 P X X' (weqtopaths _ _ w) p')). apply weqtransportb. assumption. assert (ee :forall p':P X', paths _  (u1.transportb UU0 P X X' (weqtopaths _ _ w) p') (R X X' w p')). intro.  apply (pathsinv0 _ _ _ (e p')). clear e. 

assert (is1:isweq _ _ (u1.transportb UU0 P X X' (weqtopaths _ _ w))). apply isweqtransportb10.  
apply (isweqhomot _ _ (u1.transportb UU0 P X X' (weqtopaths X X' w)) (fun p' : P X' => R X X' w p') ee is1).  Defined. 



    

(** Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)




Theorem isweqcompwithweq (X X':UU0)(w: weq X X')(Y:UU0): isweq _ _ (fun f:X'->Y => (fun x:X => f (w x))).
Proof. intros. 
set (P:= fun X0:UU0 => (X0 -> Y)). 
set (R:= fun X0:UU0 => (fun X0':UU0 => (fun w1:X0 -> X0' =>  (fun  f:P X0'  => (fun x:X0 => f (w1 x)))))). 
set (r:= fun X0:UU0 => (fun f:X0 -> Y => pathsinv0 _ _ _ (etacor X0 Y f))).
apply (isweqweqtransportb P R r X X' w). Defined.




(** ** Proof of the functional extensionality for functions *)





Lemma eqcor0 (X X':UU0)(w: weq X X')(Y:UU0)(f1 f2:X'->Y):  (paths _ (fun x:X => f1 (w x))  (fun x:X => f2 (w x))) -> paths _ f1 f2. 
Proof. intros. apply (pathsweq2 _ _ (fun f:X'->Y => (fun x:X => f (w x))) (isweqcompwithweq _ _ w Y) f1 f2). assumption.  Defined. 


Lemma apathpr1topr2 (T:UU0) : paths _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z)).
Proof. intro. apply (eqcor0 _ _  (weqpair _ _ (deltap T) (isweqdeltap T)) _ (fun z: pathsspace T => pr21 _ _ z) (fun z: pathsspace T => pr21 _ _ (pr22 _ _ z))  (idpath _ (fun t:T => t))). Defined.     


Theorem funextfun (X:UU0)(Y:UU0)(f1:X->Y)(f2:X->Y)(e: forall x:X, paths _ (f1 x) (f2 x)): paths _ f1 f2.
Proof. intros. set (f:= (fun x:X => pathsspacetriple Y (f1 x) (f2 x) (e x))).  set (g1:= (fun z:pathsspace Y => pr21 _ _ z)). set (g2:= fun z: pathsspace Y => pr21 _ _ (pr22 _ _ z)). assert (e': paths _ g1 g2). apply (apathpr1topr2 Y). assert (ee:paths _ (fun x:X => f1 x) (fun x:X => f2 x)). apply (maponpaths2b _ _ _ f g1 g2 e').  apply etacoronpaths.  assumption. Defined. 



(* End of the file univ01.v *)






