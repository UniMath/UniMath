(** * Semantics for boolean formulas. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Examples.Bool.
Require Import UniMath.Algebra.Universal.Equations.

Open Scope stn.

Definition Vars := make_varspec bool_signature natset (λ _, tt).
Definition σ := vsignature bool_signature Vars.
Definition T := vterm bool_signature Vars tt.

Definition falseb : T         := build_term_curried (inl (●0) : names σ).
Definition trueb  : T         := build_term_curried (inl (●1) : names σ).
Definition notb   : T → T     := build_term_curried (inl (●2) : names σ).
Definition andb   : T → T → T := build_term_curried (inl (●3) : names σ).
Definition orb    : T → T → T := build_term_curried (inl (●4) : names σ).

Definition interp (α: assignment bool_algebra Vars) (t: T) : bool :=
  fromvterm (ops bool_algebra) α tt t.

(** ** Examples. *)

Definition x : T := varterm (0: Vars).
Definition y : T := varterm (1: Vars).
Definition z : T := varterm (2: Vars).

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
