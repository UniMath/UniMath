(** * Addendum to the file univalence_for_hProp 

This file contains the results on [ hProp ] requiring the univalence and the resizing axiom

RA2 [ hProp : UU0 ] is valid. *)


(** *** Preambule *)

Add Rec LoadPath "../Generalities".


Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp_up.



Corollary isasethProp : isaset hProp.
Proof. apply (u1isasettou0isaset _ uu1isasethProp). Defined. 




(* End of the file univalence_for_hProp_r.v *)