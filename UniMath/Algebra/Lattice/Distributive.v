(** * Distributive lattices *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.

Section Def.

  Context {X : hSet} (L : lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).

  Definition is_distributive : hProp.
  Proof.
    use hProppair.
    - exact (∏ x y z : X, x ⊗ (y ⊕ z) = ((x ⊗ y) ⊕ (x ⊗ z))).
    - do 3 (apply impred; intro); apply setproperty.
  Defined.

End Def.

Definition distributive_lattice : UU :=
  ∑ (X : hSet) (L : lattice X), is_distributive L.