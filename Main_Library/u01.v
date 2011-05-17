

(** ** Imports. *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Require Export u0.
Require Export u1.


(** Note: since the file u1.v is imported last, the current agreement in Coq implies that  [paths] is the same as [u1.paths], [weq] is the same as [u1.weq] etc. while to access identifiers from u0.v one has to write explicitly [u0.paths] etc. *)



(** * The hierarchy of universes. *)

(** The following definitions establish the hierarchy of universes such that UU0=u0.UU, UU1=u1.UU,  UU0:UU1 and UU0 is a subtype of UU1**)

Notation UU0:=u0.UU.
Notation UU1:=u1.UU.

Definition j01:UU0 -> UU1:= fun T:UU0 => T. 
Definition j11:UU1 -> UU1:= fun T:UU1 => T.

Definition UU0inUU1:= j11 UU0.

Identity Coercion totype0: UU0 >-> Sortclass.
Identity Coercion totype1: UU1 >-> Sortclass.

(** Some connections between u0 and u1 definitions. *)

Theorem u1pathstou0paths : forall (X:UU0)(x x':X), paths _ x x' -> u0.paths _ x x'.
Proof.  intros.  destruct X0. apply u0.idpath. Defined.

Theorem u0pathstou1paths: forall (X:UU0)(x x':X), u0.paths _ x x' -> paths _ x x'.
Proof. intros. destruct X0. apply idpath. Defined. 

Theorem iswequ1pathstou0paths (X:UU0)(x x':X): isweq _ _ (u1pathstou0paths _ x x').
Proof. intros. set (f:=u1pathstou0paths _ x x'). set (g:= u0pathstou1paths _ x x').
assert (egf: forall a:_,  paths _ (g (f a)) a). intros. destruct a. simpl.  apply idpath. 
assert (efg: forall a:_, paths _ (f (g a)) a). intros. destruct a. simpl. apply idpath.
apply (gradth _ _ _ _ egf efg). Defined. 

Coercion u1pathstou0paths: paths >-> u0.paths.

Theorem u1iscontrtou0iscontr (X:UU0): iscontr X -> u0.iscontr X.
Proof. intros. split with (pr21 _ _ X0). 
intro.  set (s:=contrl2 X X0 t (pr21 X (fun cntr : X => forall t0 : X, paths X t0 cntr) X0)). apply (u1pathstou0paths X t _ s). Defined.

Coercion  u1iscontrtou0iscontr: iscontr >-> u0.iscontr.


Theorem u0iscontrtou1iscontr (X:UU0): u0.iscontr X -> iscontr X.
Proof. intros. split with (u0.pr21 _ _ X0). 
 intro. apply (u0pathstou1paths _ t _). apply (u0.contrl2 X X0 _ _ ). Defined.

Coercion u0iscontrtou1iscontr: u0.iscontr  >-> iscontr.
 
Theorem u1isofhleveltou0isofhlevel (n:nat)(X:UU0): isofhlevel n X -> u0.isofhlevel n X.
Proof. intro. induction n. intro.  apply u1iscontrtou0iscontr. intro. simpl. intro. intros. set (s:= X0 x x'). 
set (s1:=isofhlevelweqf n _ _  (u1pathstou0paths X x x') (iswequ1pathstou0paths X x x') s). apply (IHn _ s1).
Defined.

Coercion  u1isofhleveltou0isofhlevel: isofhlevel >-> u0.isofhlevel.


Theorem u0isofhleveltou1isofhlevel  (n:nat)(X:UU0): u0.isofhlevel n X -> isofhlevel n X.
Proof. intro. induction n.  intro.  apply u0iscontrtou1iscontr. intros. simpl. intros.  
assert (s:isofhlevel n (u0.paths _ x x')). apply (IHn _ (X0 x x')). apply (isofhlevelweqb n _ _ _ (iswequ1pathstou0paths _ x x') s). Defined.  

Coercion u0isofhleveltou1isofhlevel: u0.isofhlevel >-> isofhlevel.






(** * Types of properties and sets in UU0 *)




Definition hProp:= (total2 UU0 (fun X:UU0 => isaprop X)).
Definition hProppair:= (tpair  UU0 (fun X:UU0 => isaprop X)).
Definition hptouu0 := pr21  UU0 (fun X:UU0 => isaprop X): hProp -> UU0.
Coercion hptouu0: hProp >-> UU0.

(** Assuming the univalence axiom one can prove

Theorem isasethProp: isaset hProp.

*)



Definition hSet0:= (total2 UU0 (fun X:UU0 => isaset X)).
Definition hSet0pair := (tpair UU0 (fun X:UU0 => isaset X)).
Definition hs0touu0:= pr21 UU0 (fun X:UU0 => isaset X) : hSet0 -> UU0.
Coercion hs0touu0: hSet0 >-> UU0.


(** * Relations *)


Definition hrel (X:UU1) := forall x1 x2 : X, hProp.

Definition isrefl (X:UU1)(R:hrel X) := forall x:X, R x x.

Definition issymm (X:UU1)(R:hrel X):= forall x1 x2 : X, R x1 x2 -> R x2 x1.

Definition istrans (X:UU1) (R: hrel X):= forall x1 x2 x3 : X, forall (f1: R  x1 x2) (f2: R x2 x3), R x1 x3.

Definition iseqrel (X:UU1)(R:hrel X):= dirprod (isrefl _ R) (dirprod (issymm _ R) (istrans _ R)).

Lemma isapropiseqclass  (X:UU1)(R:hrel X): isaprop (iseqrel _ R).
Proof. intros.
unfold iseqrel. apply isofhleveldirprod. apply impred. intro. apply (pr22 _ _ (R t t)).  apply isofhleveldirprod. apply impredtwice. intros. apply impred. intro. apply (pr22 _ _ (R t' t)). apply impred.  intro. apply impred. intro. apply impred.  intro. apply impred. intro. apply impred.  intro.  apply (pr22 _ _ (R t t1)).  Defined. 


(** * Types of subsets *)



Definition hsubtypes (X:UU1) := (X -> hProp):UU1.

(** Assuming univalence axiom one can prove 

Theorem isasethsubtypes (X:UU1): isaset (hsubtypes X).

*)


Definition carrier (X:UU1)(A:hsubtypes X):= total2 X (fun x:X => A x).
Definition carrierpair (X:UU1)(A:hsubtypes X):= tpair X (fun x:X => A x).
Coercion carrier: hsubtypes >-> UU1.

Definition carrierincl (X:UU1)(A:hsubtypes X):= (pr21 _ _) : carrier X A -> X.



(* End of the file u01.v *)






