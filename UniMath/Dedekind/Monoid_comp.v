(** * Complements about monoids and abelian monoids *)
(* split ?*)

(** Catherine Lelay. Oct. 2015 - *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Ktheory.Monoid.
Require Export UniMath.Ktheory.AbelianMonoid.

(** ** More about isunital *)

Definition unel_isunital {X : hSet} {op : binop X} (is : isunital op) : X := pr1 is.
Definition islunit_isunital {X : hSet} {op : binop X} (is : isunital op):
  (∀ x : X, op (unel_isunital is) x = x) :=
  pr1 (pr2 is).
Definition isrunit_isunital {X : hSet} {op : binop X} (is : isunital op):
  (∀ x : X, op x (unel_isunital is) = x) := pr2 (pr2 is).

(** ** More abour monoids *)

(** - assocax_is: ∀ (X : hSet) (opp : binop X), ismonoidop opp -> isassoc opp
  - unel_is: ∀ (X : hSet) (opp : binop X), ismonoidop opp -> X
  - lunax_is:
  ∀ (X : hSet) (opp : binop X) (is : ismonoidop opp),
  islunit opp (unel_is is)
  - runax_is:
  ∀ (X : hSet) (opp : binop X) (is : ismonoidop opp),
  isrunit opp (unel_is is) *)
           
Definition op_monoid (X : monoid) : binop X := op.
(** - assocax: ∀ X : monoid, isassoc op_monoid
  - unel: ∀ X : monoid, X
  - lunax: ∀ X : monoid, islunit op (unel X)
  - runax: ∀ X : monoid, isrunit op (unel X) *)
