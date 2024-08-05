(** * Distributive lattices *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Complement.

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

Definition make_distributive_lattice {X : hSet} {l : lattice X} (i : is_distributive l) : distributive_lattice := (X,,l,,i).

Definition distributive_lattice_is_distributive (l : distributive_lattice) := pr22 l.

Definition distributive_lattice_to_lattice (l : distributive_lattice) : lattice (pr1 l) := pr1 (pr2 l).
Coercion distributive_lattice_to_lattice : distributive_lattice >-> lattice.

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

Section Properties.
  Lemma distrlattice_Lmax_ldistr  (l : distributive_lattice) : isldistr (Lmax l) (Lmin l) .
  Proof .
    intros ? ? ?. use (distributive_lattice_is_distributive l) .
  Defined .

  Lemma distrlattice_Lmax_rdistr (l : distributive_lattice) : isrdistr (Lmax l) (Lmin l) .
  Proof.
    use weqldistrrdistr.
    - use iscomm_Lmin.
    - intros ? ? ?. use (distributive_lattice_is_distributive l).
  Defined.

  Lemma dual_lattice_is_distributive (l : distributive_lattice) : is_distributive (dual_lattice l) .
  Proof.
    assert (isldistr (Lmin l) (Lmax l) ) as d.
    {
      intros ? b c .
      rewrite ((distributive_lattice_is_distributive l) (Lmax _ _ _) c b).
      rewrite (iscomm_Lmin _ (Lmax _ _ _) _).
      rewrite (Lmin_absorb) .
      rewrite distrlattice_Lmax_rdistr.
      rewrite <- (isassoc_Lmax _ c).
      rewrite (Lmax_absorb).
      reflexivity.
    }
    intros ? ? ?.
    use d .
  Defined.

  Lemma distrlattice_Lmin_ldistr (l : distributive_lattice) : isldistr (Lmin l) (Lmax l) .
  Proof.
    exact (distrlattice_Lmax_ldistr (make_distributive_lattice (dual_lattice_is_distributive l))).
  Defined.

  Lemma distrlattice_Lmin_rdistr (l : distributive_lattice): isrdistr (Lmin l) (Lmax l) .
  Proof.
    exact (distrlattice_Lmax_rdistr (make_distributive_lattice (dual_lattice_is_distributive l))).
  Defined.
End Properties.
