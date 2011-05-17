


(** * Univalence axiom and functional extensionality. 

This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun. 

This proof requires one to use some of the general definitions and results of the univalent approach both for the universe for which funextfun is being proved and for the universe which is one level higher.  

The new proof of functional extensionality for the dependent functions from the functional extensionality of usual functions given in uu?.v makes it unnessesary to use three universe levels to deduce extensionality for dependent functions from the univalence axiom and in particular makes it unnessecary to have two files with the univalence  axiom.  
   
*)


(** *** Preamble. *)

Add Rec LoadPath "../Main_Library/Generalities".

(** *** Imports. *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Require Export uu1uu0.


(** ** Univalence axiom. *)


Definition eqweqmap (T1:UU0) (T2:UU0) : (uu1.paths _ T1 T2) -> (weq T1 T2).
Proof. intros. induction X. apply idweq. Defined. 

Axiom univalenceaxiom: forall T1:UU0, forall T2:UU0, uu1.isweq (uu1.paths _ T1 T2) (weq T1 T2) (eqweqmap T1 T2).
 
Definition weqtopaths (T1:UU0)(T2:UU0)(w: weq T1 T2) : uu1.paths _ T1 T2 := uu1.invmap _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.


Definition weqpathsweq (T1:UU0)(T2:UU0)(w: weq T1 T2):uu1.paths _ (eqweqmap _ _ (weqtopaths _ _ w)) w := uu1.weqfg _ _ (eqweqmap T1 T2) (univalenceaxiom T1 T2) w.

(** Conjecture: univalenceaxiom is equivalent to two axioms 

[Axiom weqtopaths0 (T1:UU0)(T2:UU0)(w: weq T1 T2): paths1 _ T1 T2.]

[Axiom weqpathsweq0 (T1:UU0)(T2:UU0)(w: weq T1 T2):paths1 _ (eqweqmap0 _ _ (weqtopaths0 _ _ w)) (weqpair0 _ _ w).]

 *)

Axiom weqtopaths0: forall (T1:UU0)(T2:UU0)(w:weq T1 T2), uu1.paths _ T1 T2.

Axiom weqpathsweq0: forall (T1:UU0)(T2:UU0)(w:weq T1 T2), uu1.paths _ (eqweqmap _ _ (weqtopaths0 _ _ w)) w.

Theorem univfromtwoaxioms: forall T1:UU0, forall T2:UU0, uu1.isweq (uu1.paths _ T1 T2) (weq T1 T2) (eqweqmap T1 T2).
Proof. intros. set (P1:= fun XY: uu1.dirprod UU0 UU0 => (match XY with uu1.tpair X Y => uu1.paths _ X Y end)). set (P2:= fun XY: uu1.dirprod UU0 UU0 => match XY with uu1.tpair X Y => weq X Y end). set (Z1:= uu1.total2 _ P1). set (Z2:= uu1.total2 _ P2). set (f:= (uu1.totalfun _ _ _ (fun XY:uu1.dirprod UU0 UU0 => (match XY with uu1.tpair X Y => eqweqmap X Y end))): Z1 -> Z2). set (g:=  (uu1.totalfun _ _ _ (fun XY:uu1.dirprod UU0 UU0 => (match XY with uu1.tpair X Y => weqtopaths0 X Y end))): Z2 -> Z1). set (s1:= (fun X Y :UU0 => fun w: weq X Y => uu1.tpair _ P2 (uu1.dirprodpair _ _ X Y) w)). set (efg:= (fun a:_ => match a as a' return (uu1.paths _ (f (g a')) a') with uu1.tpair (uu1.tpair X Y) w => (uu1.maponpaths _ _ (s1 X Y) _ _ (weqpathsweq0 X Y w)) end)). 

set (h:= fun a1:Z1 => (uu1.pr21 _ _ (uu1.pr21 _ _ a1))).
assert (egf0: forall a1:Z1, uu1.paths (uu1.dirprod UU0 UU0) (uu1.pr21 _ _ (g (f a1))) (uu1.pr21 _ _ a1)). intro. apply uu1.idpath.  
assert (egf1: forall a1 a1':Z1, uu1.paths _ (uu1.pr21 _ _ a1') (uu1.pr21 _ _ a1) -> uu1.paths _ a1' a1). intros.  set (X':= uu1.maponpaths _ _ (uu1.pr21 _ _ ) _ _ X). 
assert (is: uu1.isweq _ _ h).  apply (uu1.isweqpr21pr21). apply (uu1.pathsweq2 _ _ h is _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:=uu1.gradth _ _ _ _ egf efg). 
apply (uu1.isweqtotaltofib _ P1 P2  (fun XY:uu1.dirprod UU0 UU0 => (match XY with uu1.tpair X Y => eqweqmap X Y end)) is2 (uu1.dirprodpair _ _ T1 T2)). Defined. 


(** Conjecture: the pair [weqtopaths0] and [weatopathsweq0] is well defined up to a canonical equality. **)






(** ** Transport theorem. 

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:uu1.paths _ x x'): isweq _ _ (uu1.transportf X P x x' e).
Proof. intros. induction e.  apply idisweq. Defined.

Lemma isweqtransportb10 (X:UU1)(P:X -> UU0)(x:X)(x':X)(e:uu1.paths _ x x'): isweq _ _ (uu1.transportb X P x x' e).
Proof. intros. apply (isweqtransportf10 _ _ _ _ (uu1.pathsinv0 _ _ _ e)). Defined. 



Lemma l1  (X0:UU0)(X0':UU0)(ee: uu1.paths _ X0 X0')(P:UU0 -> UU0)(pp': P X0')(R: forall X:UU0, forall X':UU0, forall w: weq X X', P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p):paths _ (R X0 X0' (eqweqmap _ _ ee) pp') (uu1.transportb UU0 P X0 X0' ee pp').
Proof. intro. intro. intro. intro. intro. induction ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb  (P:UU0 -> UU0)(R: forall (X X':UU0) (w: weq X X'), P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU0) (w: weq X X') (p':P X'), paths _ (R X X' w p') (uu1.transportb UU0  P X X' (weqtopaths _ _ w) p').  
Proof. intros. set (uv:=weqtopaths _ _ w).   set (v:=eqweqmap _ _ uv). 

assert (e:uu1.paths _ v w). unfold weqtopaths in uv.  apply (uu1.weqfg  (uu1.paths UU0 X X') (weq X X')  (eqweqmap X X') (univalenceaxiom X X') w).

assert (ee:uu1.paths _ (R X X' v p') (R X X' w p')). set (R':= fun vis:weq X X' => R X X' vis p'). assert (ee':uu1.paths _ (R' v) (R' w)). apply (uu1.maponpaths (weq X X') (P X) R' _ _ e). assumption.

induction ee. apply l1. assumption. Defined.



Corollary isweqweqtransportb (P:UU0 -> UU0)(R: forall (X X':UU0) (w: weq X X'), P X' -> P X)(r: forall X:UU0, forall p:P X, paths _ (R X X (idweq X) p) p): forall (X X':UU0)(w: weq X X'), isweq _ _ (fun p': P X' => R X X' w p').
Proof. intros. assert (e:forall p':P X', paths _ (R X X' w p') (uu1.transportb UU0 P X X' (weqtopaths _ _ w) p')). apply weqtransportb. assumption. assert (ee :forall p':P X', paths _  (uu1.transportb UU0 P X X' (weqtopaths _ _ w) p') (R X X' w p')). intro.  apply (pathsinv0 _ _ _ (e p')). clear e. 

assert (is1:isweq _ _ (uu1.transportb UU0 P X X' (weqtopaths _ _ w))). apply isweqtransportb10.  
apply (isweqhomot _ _ (uu1.transportb UU0 P X X' (weqtopaths X X' w)) (fun p' : P X' => R X X' w p') ee is1).  Defined. 



    

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






