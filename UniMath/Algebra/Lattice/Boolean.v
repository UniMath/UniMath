(** * Boolean algebras *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Complement.
Require Import UniMath.Algebra.Lattice.Distributive.
Require Import UniMath.Algebra.Lattice.Heyting.

Section Def.

  Context {X : hSet} (L : bounded_lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).
  Local Notation "⊤" := (Ltop L).
  Local Notation "⊥" := (Lbot L).

  (** While complements are in general not unique, we regain uniqueness in the
      case of Boolean algebras. Therefore, Boolean algebra structure is a proposition. *)
  Definition is_boolean : hProp.
  Proof.
    use make_hProp.
    - refine (∑ is_distr : is_distributive L, _).
      use make_hProp.
      + exact (complemented_structure L).
      + apply impred; intro.
        apply distributive_lattice_complements_are_unique; auto.
    - abstract (apply isaprop_total2).
  Defined.

End Def.

Definition make_is_boolean {X : hSet} (L : bounded_lattice X) :
  is_distributive L -> complemented_structure L -> is_boolean L.
Proof.
  intros ? ?.
  use tpair.
  - assumption.
  - assumption.
Defined.

Definition boolean_algebra (X : hSet) :=
  ∑ L : bounded_lattice X, is_boolean L.

Section Accessors.
  Context {X : hSet} (B : boolean_algebra X).

  Definition boolean_algebra_lattice  : bounded_lattice X :=
    pr1 B.

  Definition boolean_algebra_is_boolean :
    is_boolean boolean_algebra_lattice := pr2 B.

  Definition boolean_algebra_complement : complemented_structure boolean_algebra_lattice :=
    pr2 (pr2 B).

End Accessors.

Coercion boolean_algebra_lattice : boolean_algebra >-> bounded_lattice.

(** Every Boolean algebra has eponentials (is a Heyting algebra). *)
Section Heyting.

  Context {X : hSet} (L : boolean_algebra X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ⊕ y" := (Lmax L x y).
  Local Notation "¬ x" := (boolean_algebra_complement L x).

  Lemma boolean_algebra_exponential : exponential L.
  Proof.
    use make_exponential.
    - intros x y; exact ((¬ x) ⊕ y).
    - intros x y z; use make_dirprod; cbn; intros H.
  Abort.
End Heyting.
