(** * Example on booleans *)

(**
  This file contains the definition of the signature of booleans and the standard boolean algebra.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope stn.

Definition bool_signature := make_signature_simple_single_sorted [0; 0; 1; 2; 2 ].

Definition bool_sort: sorts bool_signature := tt.

Definition bool_false_op : names bool_signature := ●0.
Definition bool_true_op : names bool_signature := ●1.
Definition bool_not_op : names bool_signature := ●2.
Definition bool_and_op : names bool_signature := ●3.
Definition bool_or_op : names bool_signature := ●4.

Definition bool_algebra := make_algebra_simple_single_sorted bool_signature boolset
  [(
    λ _, false ;
    λ _, true ; 
    λ x, negb (pr1 x) ;
    λ x, andb (pr1 x) (pr12 x) ; 
    λ x, orb (pr1 x) (pr12 x)
  )].

Definition bool_false := build_term_curried bool_false_op.
Definition bool_true := build_term_curried bool_true_op.
Definition bool_not := build_term_curried bool_not_op.
Definition bool_and := build_term_curried bool_and_op.
Definition bool_or := build_term_curried bool_or_op.
