(** * Functions connecting the constructions from uu0 and uu1.

 This file contains the definitions of functions related the constructions of uu0.v to constructiopns of uu1.v under the asumption that the universe UU0 := u0.UU
 is a sub-universe of UU1 := uu1.UU . The need for this file should disappear when a better universe management is implemented in Coq. *)


(** *** Preambule *)

Add Rec LoadPath "../Generalities".


Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export uuu uu1 uu0.


(** *** Universe structure *)

Notation UU0 := uu0.UU.
Notation UU1 := uu1.UU.

Definition j01:UU0 -> UU1:= fun T:UU0 => T. 
Definition j11:UU1 -> UU1:= fun T:UU1 => T.

Definition UU0inUU1:= j11 UU0.


(** *** Some connections between uu0 and uu1 definitions. *)

Theorem u1pathstou0paths : forall (X:UU0)(x x':X), uu1.paths _ x x' -> paths _ x x'.
Proof.  intros.  destruct X0. apply idpath. Defined.

Theorem u0pathstou1paths: forall (X:UU0)(x x':X), paths _ x x' -> uu1.paths _ x x'.
Proof. intros X x x' X0. destruct X0. apply uu1.idpath. Defined. 

Theorem iswequ1pathstou0paths (X:UU0)(x x':X): uu1.isweq _ _ (u1pathstou0paths _ x x').
Proof. intros. set (f:=u1pathstou0paths _ x x'). set (g:= u0pathstou1paths _ x x').
assert (egf: forall a:_,  uu1.paths _ (g (f a)) a). intros. destruct a. simpl.  apply uu1.idpath. 
assert (efg: forall a:_, uu1.paths _ (f (g a)) a). intros. destruct a. simpl. apply uu1.idpath.
apply (uu1.gradth _ _ _ _ egf efg). Defined. 

Coercion u1pathstou0paths: uu1.paths >-> paths.

Theorem u1iscontrtou0iscontr (X:UU0): uu1.iscontr X -> iscontr X.
Proof. intros. split with (uu1.pr21 _ _ X0). 
intro.  set (s:=uu1.contrl2 X X0 t (uu1.pr21 X (fun cntr : X => forall t0 : X, uu1.paths X t0 cntr) X0)). apply (u1pathstou0paths X t _ s). Defined.

Coercion  u1iscontrtou0iscontr: uu1.iscontr >-> iscontr.


Theorem u0iscontrtou1iscontr (X:UU0): iscontr X -> uu1.iscontr X.
Proof. intros X X0. split with (pr21 _ _ X0). 
 intro. apply (u0pathstou1paths _ t _). apply (contrl2 X X0 _ _ ). Defined.

Coercion u0iscontrtou1iscontr: iscontr  >-> uu1.iscontr.
 
Theorem u1isofhleveltou0isofhlevel (n:nat)(X:UU0): uu1.isofhlevel n X -> isofhlevel n X.
Proof. intro. induction n. intro X0.  apply u1iscontrtou0iscontr. intro. simpl. intro. intros. set (s:= X0 x x'). 
set (s1:=uu1.isofhlevelweqf n _ _  (u1pathstou0paths X x x') (iswequ1pathstou0paths X x x') s). apply (IHn _ s1).
Defined.

Coercion  u1isofhleveltou0isofhlevel: uu1.isofhlevel >-> isofhlevel.



Theorem u0isofhleveltou1isofhlevel  (n:nat)(X:UU0): isofhlevel n X -> uu1.isofhlevel n X.
Proof. intro. induction n.  intro X0.  apply u0iscontrtou1iscontr. intro X. simpl. intros X0 x x'.  
assert (s: uu1.isofhlevel n (paths _ x x')). apply (IHn _ (X0 x x')). apply (uu1.isofhlevelweqb n _ _ _ (iswequ1pathstou0paths _ x x') s). Defined.  

Coercion u0isofhleveltou1isofhlevel: isofhlevel >-> uu1.isofhlevel.

Definition u0isaproptou1isaprop (X : UU0) := u0isofhleveltou1isofhlevel (S O) X : isaprop X -> uu1.isaprop X.
Coercion u0isaproptou1isaprop : isaprop >-> uu1.isaprop.


Definition u1isaproptou0isaprop (X : UU0) := u1isofhleveltou0isofhlevel (S O) X : uu1.isaprop X -> isaprop X.
Coercion u1isaproptou0isaprop : uu1.isaprop >-> isaprop.


Theorem u0isasettou1isaset (X: UU0) : isaset X -> uu1.isaset X.
Proof. intros X X0. unfold uu1.isaset.  unfold isaset in X0. apply u0isofhleveltou1isofhlevel. assumption.  Defined.

Coercion u0isasettou1isaset : isaset >-> uu1.isaset.

Theorem u1isasettou0isaset (X: UU0) : uu1.isaset X -> isaset X.
Proof. intros X X0. unfold isaset.  unfold uu1.isaset in X0. apply u1isofhleveltou0isofhlevel. assumption.  Defined.

Coercion u1isasettou0isaset : uu1.isaset >-> isaset.





(* End of the file uu0uu1.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)




