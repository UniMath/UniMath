

(** ** Imports. *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Require Export u2.
Require Export u1.


(** Note: since the file u1.v is imported last, the current agreement in Coq implies that  [paths] is the same as [u1.paths], [weq] is the same as [u1.weq] etc. while to access identifiers from u0.v one has to write explicitly [u0.paths] etc. *)



(** * The hierarchy of universes. *)

(** The following definitions establish the hierarchy of universes such that UU0=u0.UU, UU1=u1.UU,  UU0:UU1 and UU0 is a subtype of UU1**)

Notation UU2:=u2.UU.
Notation UU1:=u1.UU.

Definition j12:UU1 -> UU2:= fun T:UU1 => T. 
Definition j22:UU2 -> UU2:= fun T:UU2 => T.

Definition UU01inUU2:= j22 UU1.

Identity Coercion totype2: UU2 >-> Sortclass.
Identity Coercion totype1: UU1 >-> Sortclass.

(** Some connections between u2 and u1 definitions. *)

Theorem u1pathstou2paths : forall (X:UU1)(x x':X), paths _ x x' -> u2.paths _ x x'.
Proof.  intros.  destruct X0. apply u2.idpath. Defined.

Theorem u2pathstou1paths: forall (X:UU1)(x x':X), u2.paths _ x x' -> paths _ x x'.
Proof. intros. destruct X0. apply idpath. Defined. 

Theorem iswequ1pathstou2paths (X:UU1)(x x':X): u2.isweq _ _ (u1pathstou2paths _ x x').
Proof. intros. set (f:=u1pathstou2paths _ x x'). set (g:= u2pathstou1paths _ x x').
assert (egf: forall a:_,  u2.paths _ (g (f a)) a). intros. destruct a. simpl.  apply u2.idpath. 
assert (efg: forall a:_, u2.paths _ (f (g a)) a). intros. destruct a. simpl. apply u2.idpath.
apply (u2.gradth _ _ _ _ egf efg). Defined. 

Coercion u1pathstou2paths: paths >-> u2.paths.

Theorem u1iscontrtou2iscontr (X:UU1): iscontr X -> u2.iscontr X.
Proof. intros. split with (pr21 _ _ X0). 
intro.  set (s:=contrl2 X X0 t (pr21 X (fun cntr : X => forall t0 : X, paths X t0 cntr) X0)). apply (u1pathstou2paths X t _ s). Defined.

Coercion  u1iscontrtou2iscontr: iscontr >-> u2.iscontr.


Theorem u2iscontrtou1iscontr (X:UU1): u2.iscontr X -> iscontr X.
Proof. intros. split with (u2.pr21 _ _ X0). 
 intro. apply (u2pathstou1paths _ t _). apply (u2.contrl2 X X0 _ _ ). Defined.

Coercion u2iscontrtou1iscontr: u2.iscontr  >-> iscontr.
 
Theorem u1isofhleveltou2isofhlevel (n:nat)(X:UU1): isofhlevel n X -> u2.isofhlevel n X.
Proof. intro. induction n. intro.  apply u1iscontrtou2iscontr. intro. simpl. intro. intros. set (s:= X0 x x'). 
set (s1:=u2.isofhlevelweqf n _ _  (u1pathstou2paths X x x') (iswequ1pathstou2paths X x x') (IHn _ s)). assumption.
Defined.

Coercion  u1isofhleveltou2isofhlevel: isofhlevel >-> u2.isofhlevel.


Theorem u2isofhleveltou1isofhlevel  (n:nat)(X:UU1): u2.isofhlevel n X -> isofhlevel n X.
Proof. intro. induction n.  intro.  apply u2iscontrtou1iscontr. intros. simpl. intros.  
assert (s:u2.isofhlevel n (u2.paths _ x x')). apply (X0 x x').  apply (IHn _ (u2.isofhlevelweqb n _ _ _ (iswequ1pathstou2paths _ x x') s)).  Defined.  

Coercion u2isofhleveltou1isofhlevel: u2.isofhlevel >-> isofhlevel.






(** * Types of properties and sets in UU1 *)




Definition hProp1:= (u2.total2 UU1 (fun X:UU1 => isaprop X)).
Definition hProp1pair:= u2.tpair  UU1 (fun X:UU1 => isaprop X).
Definition hp1touu1 := u2.pr21  UU1 (fun X:UU1 => isaprop X): hProp1 -> UU1.
Coercion hp1touu1: hProp1 >-> UU1.


Definition hSet:= u2.total2 UU1 (fun X:UU1 => isaset X).
Definition hSet0pair := u2.tpair UU1 (fun X:UU1 => isaset X).
Definition hstouu1:= u2.pr21 UU1 (fun X:UU1 => isaset X) : hSet -> UU1.
Coercion hstouu1: hSet >-> UU1.






(* End of the file u12.v *)






