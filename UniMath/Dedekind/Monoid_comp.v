(** * Complements about monoids and abelian monoids *)
(* split ?*)

(** Catherine Lelay. Oct. 2015 - *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Ktheory.Monoid.
Require Export UniMath.Ktheory.AbelianMonoid.

(** ** Monoids *)
(** *** A new useful definition *)

Definition ismonoid {X : hSet} (x0 : X) (op : binop X) : UU :=
  (isassoc op) × (isunit op x0).
Definition ismonoid_ismonoidop {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : ismonoidop op :=
  pr1 is,, x0,, pr2 is.

Definition ismonoid_isassoc {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isassoc op :=
  pr1 is.
Definition ismonoid_islunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : islunit op x0 :=
  pr1 (pr2 is).
Definition ismonoid_isrunit {X : hSet} {x0 : X} {op : binop X} (is : ismonoid x0 op) : isrunit op x0 :=
  pr2 (pr2 is).

(** ** Abelian Monoids *)

Definition isabmonoid {X : hSet} (x0 : X) (op : binop X) : UU :=
  (ismonoid x0 op) × (iscomm op).
Definition isabmonoid_isabmonoidop {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isabmonoidop op :=
  ismonoid_ismonoidop (pr1 is),, pr2 is.

Definition isabmonoid_ismonoid {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : ismonoid x0 op :=
  pr1 is.
Definition isabmonoid_isassoc {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isassoc op :=
  ismonoid_isassoc (isabmonoid_ismonoid is).
Definition isabmonoid_islunit {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : islunit op x0 :=
  ismonoid_islunit (isabmonoid_ismonoid is).
Definition isabmonoid_isrunit {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : isrunit op x0 :=
  ismonoid_isrunit (isabmonoid_ismonoid is).
Definition isabmonoid_iscomm {X : hSet} {x0 : X} {op : binop X} (is : isabmonoid x0 op) : iscomm op :=
  pr2 is.