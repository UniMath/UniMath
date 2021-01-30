(** * Example on monoids. *)

(**
This file contains the definition of the signature of monoids and the way to turn
a monoid (as defined in [UniMath.Algebra.Monoids]) into an algebra.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.Algebra.Universal.EqAlgebras.

Local Open Scope stn.

(** Signature. *)

Definition monoid_signature := make_signature_simple_single_sorted [2; 0].

(** Algebra of monoids without equations. *)

Definition monoid_algebra (M: monoid)
  : algebra monoid_signature
  := make_algebra_simple_single_sorted monoid_signature M
  [(
    λ p, op (pr1 p) (pr12 p) ;
    λ _, unel M
  )].

Module Eqspec.

(** Free algebra of open terms. *)

Definition monoid_varspec : varspec monoid_signature
  := make_varspec monoid_signature natset (λ _, tt).

Definition Mon : UU := term monoid_signature monoid_varspec tt.
Definition mul : Mon → Mon → Mon := build_term_curried (●0: names monoid_signature).
Definition id  : Mon := build_term_curried (●1: names monoid_signature).

Definition x : Mon := varterm (0: monoid_varspec).
Definition y : Mon := varterm (1: monoid_varspec).
Definition z : Mon := varterm (2: monoid_varspec).

Definition monoid_equation : UU
  := equation monoid_signature monoid_varspec.

Definition monoid_mul_assoc : monoid_equation :=
  tt,, make_dirprod (mul (mul x y) z) (mul x (mul y z)).

Definition monoid_mul_lid : monoid_equation
  := tt,, make_dirprod (mul id x) x.

Definition monoid_mul_rid : monoid_equation
  := tt,, make_dirprod (mul x id) x.

Definition monoid_axioms : eqsystem monoid_signature monoid_varspec
  := ⟦ 3 ⟧,, three_rec monoid_mul_assoc monoid_mul_lid monoid_mul_rid.

Definition monoid_eqspec : eqspec.
Proof.
  use tpair. { exact monoid_signature. }
  use tpair. { exact monoid_varspec. }
  exact monoid_axioms.
Defined.

Definition monoid_eqalgebra := eqalgebra monoid_eqspec.

(** Every monoid is a monoid eqalgebra. *)

Section Make_Monoid_Eqalgebra.

Variable M : monoid.

Lemma holds_monoid_mul_lid : holds (monoid_algebra M) monoid_mul_lid.
Proof.
  intro. cbn in α.
  change (fromterm (monoid_algebra M) α tt (mul id x) = α 0).
  change (op (unel M) (α 0) = α 0).
  apply lunax.
Qed.

Lemma holds_monoid_mul_rid : holds (monoid_algebra M) monoid_mul_rid.
Proof.
  intro.
  change (op (α 0) (unel M) = α 0).
  apply runax.
Qed.

Lemma holds_monoid_mul_assoc : holds (monoid_algebra M) monoid_mul_assoc.
Proof.
  intro.
  change (op (op (α 0) (α 1)) (α 2) = op (α 0) (op (α 1) (α 2))).
  apply assocax.
Qed.

Definition is_eqalgebra_monoid :
  is_eqalgebra (σ := monoid_eqspec) (monoid_algebra M).
Proof.
  red. simpl.
  apply three_rec_dep; cbn.
  - exact holds_monoid_mul_assoc.
  - exact holds_monoid_mul_lid.
  - exact holds_monoid_mul_rid.
Defined.

Definition make_monoid_eqalgebra : monoid_eqalgebra.
  use make_eqalgebra.
  - exact (monoid_algebra M).
  - exact is_eqalgebra_monoid.
Defined.

End Make_Monoid_Eqalgebra.

End Eqspec.
