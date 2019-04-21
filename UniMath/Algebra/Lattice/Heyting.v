(** * Heyting algebras *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.

Section Def.

  Context {X : hSet} (L : lattice X).
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ∧ y" := (Lmin L x y).

  (** An exponential is a binary operation on [X] satisfying this law *)
  Definition exponential : UU :=
    ∑ exponential_map : X -> X -> X,
      ∏ x y z : X, z ≤ (exponential_map x y) <-> (z ∧ x) ≤ y.

  Definition exponential_map (exp : exponential) : X -> X -> X := pr1 exp.
  Coercion exponential_map : exponential >-> Funclass.

  Definition exponential_is_exponential (exp : exponential) :
    ∏ x y z : X, z ≤ (exponential_map exp x y) <-> (z ∧ x) ≤ y := pr2 exp.

End Def.