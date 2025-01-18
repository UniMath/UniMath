(** * Example on groups. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
  This file contains the definition of the signature of groups and the way to turn
  a group (as defined in [UniMath.Algebra.Groups]) into an algebra.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.MoreLists.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.Algebra.Universal.EqAlgebras.

Local Open Scope stn.
Local Open Scope eq.

(** Group structure without equations. *)

Definition group_signature := make_signature_simple_single_sorted [2; 0; 1].

Definition group_sort : sorts group_signature := tt.

Definition group_mul_op: names group_signature := ●0.
Definition group_id_op: names group_signature := ●1.
Definition group_inv_op: names group_signature := ●2.

(** Algebra of groups. *)

Module Algebra.

Definition group_algebra {G: gr}
 := make_algebra_simple_single_sorted' group_signature G [( op ; unel G; grinv G )].

Definition group_mul := build_gterm' group_mul_op.
Definition group_id  := build_gterm' group_id_op.
Definition group_inv := build_gterm' group_inv_op.

End Algebra.

Module Eqspec.

(** Equational specification and the free algebra of open terms. *)

Definition group_varspec : varspec group_signature := make_varspec group_signature natset (λ _, group_sort).
Definition G := term group_signature group_varspec group_sort.

Definition group_mul: G → G → G := build_term' group_mul_op.
Definition group_id: G := build_term' group_id_op.
Definition group_inv: G → G := build_term' group_inv_op.

Definition x : G := varterm (0: group_varspec).
Definition y : G := varterm (1: group_varspec).
Definition z : G := varterm (2: group_varspec).

Definition group_mul_assoc := group_mul (group_mul x y) z == group_mul x (group_mul y z).
Definition group_mul_lid := group_mul group_id x == x.
Definition group_mul_rid := group_mul group_id x == x.

Definition group_axioms : eqsystem group_signature group_varspec :=
  ⟦ 3 ⟧,, three_rec group_mul_assoc group_mul_lid group_mul_rid.

Definition group_eqspec : eqspec.
Proof.
  use tpair. { exact group_signature. }
  use tpair. { exact group_varspec. }
  exact group_axioms.
Defined.

Definition group_eqalgebra := eqalgebra group_eqspec.

End Eqspec.
