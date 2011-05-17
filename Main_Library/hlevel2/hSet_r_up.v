(** * Generalities on [ hSet ] requiring ( resizing ) and univalence for [ hProp ] .

*)




(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp_r_up  hSet_r.





Lemma isasethsubtypes (X:UU0): isaset (hsubtypes X).
Proof. unfold isaset. intro.  apply impred. intro. apply isasethProp. Defined.













(* End of the file hSet_r_u.v *)