Require Export Foundations.hlevel2.finitesets.

Unset Automatic Introduction.



(** To hProp.v *)

Definition forallinhprop { T : UU } ( F : T -> hProp ) : hProp.
Proof. intros. split with ( forall ( t : T ) , F t ) . apply impred . intro t . exact ( pr2 ( F t ) ) .  Defined. 


(** To hSet.v *)

(** Union of subtypes. *)

Definition union { X T : UU } ( F : T -> hsubtypes X ) : hsubtypes X := fun x : X => ishinh ( total2 ( fun t : T => F t x ) ) . 

(** Intersection of types. *)

Definition intersect { X T : UU } ( F : T -> hsubtypes X ) : hsubtypes X := fun x : X => forallinhprop ( fun t => F t x ) .   





(** Point-set topology *)


Definition topologydata ( X : UU ) := ( X -> hProp ) -> hProp . 


Definition opensets { X : UU } ( TD : topologydata X ) := total2 TD . 

Definition opensetstosubsets { X : UU } ( TD : topologydata X ) : opensets TD -> hsubtypes X := pr1  .
Coercion  opensetstosubsets : opensets >-> hsubtypes . 


Definition openunioncond { X : UU } ( TD : topologydata X ) := forall ( T : UU ) ( F : T -> opensets TD ) , TD ( union F ) . 

Definition openintcond { X : UU } ( TD : topologydata X ) := 
forall ( T : UU ) ( is : isfinite T ) ( F : T -> opensets TD ) , TD ( intersect F ) . 


Definition istopology { X : UU } ( TD : topologydata X ) := dirprod ( openunioncond TD ) ( openintcond TD ) . 

Definition topology ( X : UU ) := total2 ( fun TD : topologydata X => istopology TD ) . 

Definition topologytotopologydata ( X : UU ) : topology X -> topologydata X := pr1 . 
Coercion topologytotopologydata : topology >-> topologydata . 

Definition topologyconstr { X : UU } ( TD : topologydata X ) ( unionax : openunioncond TD ) ( intersectax : openintcond TD ) :
 topology X := ( tpair _ TD ( dirprodpair unionax intersectax ) ) . 


Definition toptype := total2 ( fun X : UU => topology X ) . 

Definition toptypecarrier : toptype -> UU := pr1 . 
Coercion toptypecarrier : toptype >-> UU . 

Definition toptypeconstr { X : UU } ( TD : topologydata X ) ( unionax : openunioncond TD ) ( intersectax : openintcond TD ) :
 toptype := tpair _ X ( tpair _ TD ( dirprodpair unionax intersectax ) ) .  


(** Discrete topologies *)


 


