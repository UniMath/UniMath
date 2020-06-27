(** * Semantics for boolean formulas. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Bool.
Require Import UniMath.Algebra.Universal.Equations.
Require Import UniMath.Algebra.Universal.Bool.

Open Scope stn.

Definition σ := vsignature bool_signature.
Definition T := vterm bool_signature.

Definition falseb : T         := build_term_curried (inl (●0) : names σ).
Definition trueb  : T         := build_term_curried (inl (●1) : names σ).
Definition notb   : T → T     := build_term_curried (inl (●2) : names σ).
Definition andb   : T → T → T := build_term_curried (inl (●3) : names σ).
Definition orb    : T → T → T := build_term_curried (inl (●4) : names σ).

Definition interp (v:nat->bool) (x:T) : bool
  := fromvterm (op bool_algebra) v x.

(** ** Examples. *)

Definition x : T := var 0.
Definition y : T := var 1.
Definition z : T := var 2.

Definition f (n : nat) : bool.
Proof.
  induction n as [|n Hn].
  - exact true.
  - exact false.
Defined.

(** ** Tests. *)
Eval lazy in interp f (andb x trueb).
Eval lazy in interp f (andb x y).
Eval lazy in interp f (orb x y).
Eval lazy in interp f (orb x (andb y falseb)).
