(** * Complements *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.

Section Def.
  Context {X : hSet} (L : bounded_lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).
  Local Notation "⊤" := (Ltop L).
  Local Notation "⊥" := (Lbot L).

  Definition complement (x : X) : UU :=
    ∑ y : X, (x ⊕ y = ⊤) × (x ⊗ y = ⊥).

  Definition complement_to_element {x : X} (y : complement x) : X := pr1 y.
  Coercion complement_to_element : complement >-> pr1hSet.

  Definition complement_top_axiom (x : X) (y : complement x) : x ⊕ y = ⊤ :=
    dirprod_pr1 (pr2 y).

  Definition complement_bottom_axiom (x : X) (y : complement x) : x ⊗ y = ⊥ :=
    dirprod_pr2 (pr2 y).

  (** This is _not_ a proposition: complements need not be unique. *)
  Definition complemented_structure : UU := ∏ x : X, complement x.

End Def.