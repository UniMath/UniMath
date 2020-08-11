(** * Decidable sets *)

(**
This file contains the definition of a decidable set, i.e., a type X endowed with the property "isdeceq X",
just like an hSet is a type X endowed with the property "isaset X".
*)

Require Import UniMath.Foundations.All.

Definition decSet: UU := ∑ (X: UU), isdeceq X.

Definition make_decSet (X: UU) (i: isdeceq X) := X,, i.

Definition pr1decSet: decSet -> UU := pr1.

Coercion pr1decSet: decSet >-> UU.

Definition decproperty (X: decSet) := pr2 X.