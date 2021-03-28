(** * Example on booleans. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
  This file contains the definition of the signature of booleans and the standard boolean algebra.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.MoreLists.

Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.VTerms.

Local Open Scope stn.

Definition bool_signature := make_signature_simple_single_sorted [0; 0; 1; 2; 2; 2].

(** ** Algebra structure over type bool. *)

Definition bool_algebra := make_algebra_simple_single_sorted' 
  bool_signature
  boolset
  [( false ; true ; negb ; andb ; orb ; implb )].

Definition bool_sort: sorts bool_signature := tt.

(** ** Boolean ground terms. *)

Module GTerm.

(** The type of ground terms. *)

Definition T := gterm bool_signature bool_sort.

(** Constructors for ground terms. *)

Definition bot  : T         := build_gterm' (●0 : names bool_signature).
Definition top  : T         := build_gterm' (●1 : names bool_signature).
Definition neg  : T → T     := build_gterm' (●2 : names bool_signature).
Definition conj : T → T → T := build_gterm' (●3 : names bool_signature).
Definition disj : T → T → T := build_gterm' (●4 : names bool_signature).
Definition impl : T → T → T := build_gterm' (●5 : names bool_signature).

End GTerm.

(** ** Booleans terms and semantics for boolean formulae. *)

Module Term.

Definition bool_varspec := make_varspec bool_signature natset (λ _, bool_sort).

(** Type for boolean (open) terms. *)

Definition T := term bool_signature bool_varspec bool_sort.

(** Constructors for terms. *)

Definition bot  : T         := build_term' (●0 : names bool_signature).
Definition top  : T         := build_term' (●1 : names bool_signature).
Definition neg  : T → T     := build_term' (●2 : names bool_signature).
Definition conj : T → T → T := build_term' (●3 : names bool_signature).
Definition disj : T → T → T := build_term' (●4 : names bool_signature).
Definition impl : T → T → T := build_term' (●5 : names bool_signature).

(** Interpretation of propositional formulae. *)

Definition interp (α: assignment bool_algebra bool_varspec) (t: T) : bool :=
  fromterm (ops bool_algebra) α bool_sort t.

(** Computations and interactive proofs. *)

Module Tests.

Definition x : T := varterm (0: bool_varspec).
Definition y : T := varterm (1: bool_varspec).
Definition z : T := varterm (2: bool_varspec).

(** Example: evaluation of true & false *)

Eval lazy in interp (λ n, false) (conj top bot).

(** A simple evaluation function for variables:
    assign true to x and y (the 0th and 1st variable) and false otherwise.
*)

Definition v n :=
  match n with
    0 => true
  | 1 => true
  | _ => false
  end.

(** Example: evaluation of x ∧ (¬ y ∧ z) *)

Eval lazy in
    interp v (conj x (conj (neg  y) z)).

(** Example: evaluation of x ∧ (z → ¬ y) *)

Eval lazy in
    interp v (conj x (impl z (neg  y))).

(** Dummett tautology *)

Local Lemma Dummett : ∏ i, interp i (disj (impl x y) (impl y x)) = true.
Proof.
  intro i. lazy.
  induction (i 0); induction (i 1); apply idpath.
Qed.

(** x ∨ ¬ (y ∧ z → x) *)

Local Lemma not_tautology : ∑ i, interp i (disj x (neg (impl (conj y z) x))) = false.
Proof.
  use tpair.
 - exact (λ n, match n with  _ => false end).
 - lazy.
   apply idpath.
Qed.

(** Further tests. *)

Definition f (n : nat) : bool.
Proof.
  induction n as [|n Hn].
  - exact true.
  - exact false.
Defined.

Eval lazy in interp f (conj x top).
Eval lazy in interp f (conj x y).
Eval lazy in interp f (disj x y).
Eval lazy in interp f (disj x (conj y bot)).

End Tests.

End Term.
