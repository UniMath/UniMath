(** * Distributive lattices *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Complement.

Section Def.

  Context {X : hSet} (L : lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).

  Definition is_distributive : hProp.
  Proof.
    use make_hProp.
    - exact (∏ x y z : X, x ⊗ (y ⊕ z) = ((x ⊗ y) ⊕ (x ⊗ z))).
    - do 3 (apply impred; intro); apply setproperty.
  Defined.

End Def.

Definition distributive_lattice : UU :=
  ∑ (X : hSet) (L : lattice X), is_distributive L.

Section Bounded.
  Context {X : hSet} (L : bounded_lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).

  Lemma distributive_lattice_complements_are_unique :
    is_distributive L -> ∏ x, isaprop (complement L x).
  Proof.
    intros is_distr x; apply invproofirrelevance; intros b a.
    apply subtypePath.
    - intro. apply isapropdirprod; apply setproperty.
    - refine (!islunit_Lmin_Ltop L (pr1 b) @ _ @ islunit_Lmin_Ltop L (pr1 a)).
      refine (_ @ maponpaths (fun z => Lmin L z _) (complement_top_axiom _ _ b)).
      refine (iscomm_Lmin _ _ _ @ _ @ iscomm_Lmin _ _ _).
      refine (!maponpaths (fun z => Lmin L _ z) (complement_top_axiom _ _ a) @ _).
      refine (is_distr _ _ _ @ _ @ !is_distr _ _ _).

      refine (iscomm_Lmax _ _ _ @ _ @iscomm_Lmax _ _ _ ).
      refine (maponpaths _ (iscomm_Lmin _ _ _) @ _ @ maponpaths _ (iscomm_Lmin _ _ _)).
      refine (maponpaths _ (complement_bottom_axiom _ _ b) @ _).
      refine (_ @ !maponpaths _ (complement_bottom_axiom _ _ a)).
      refine (_ @ maponpaths (fun z => Lmax L z _) (iscomm_Lmin _ _ _)).
      reflexivity.
  Qed.

End Bounded.
