(** * Example on groups *)

(**
  This file contains the definition of the signature of groups and the way to turn
  a group into an algebra.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope stn.

Definition group_signature := make_signature_simple_single_sorted [2; 0; 1].

Definition group_sort: sorts group_signature := tt.

Definition group_mul_op: names group_signature := ●0.
Definition group_id_op: names group_signature := ●1.
Definition group_inv_op: names group_signature := ●2.

Section GroupAlgebra.

  Context (G: gr).

  Definition group_algebra := make_algebra_simple_single_sorted group_signature G
    [(
      λ p, op (pr1 p) (pr12 p) ;
      λ _, unel G ;
      λ p, grinv G (pr1 p)
    )].

End GroupAlgebra.

Definition group_mul := build_term_curried group_mul_op.
Definition group_id  := build_term_curried group_id_op.
Definition group_inv := build_term_curried group_inv_op.
