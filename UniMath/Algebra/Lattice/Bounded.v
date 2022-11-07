(** * Bounded lattices *)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Lattice.Lattice.

Definition bounded_latticeop {X : hSet} (l : lattice X) (bot top : X) :=
  (islunit (Lmax l) bot) × (islunit (Lmin l) top).

Definition bounded_lattice (X : hSet) :=
  ∑ (l : lattice X) (bot top : X), bounded_latticeop l bot top.

Definition make_bounded_lattice {X : hSet} {l : lattice X} {bot top : X} :
  bounded_latticeop l bot top → bounded_lattice X := λ bl, l,, bot,, top,, bl.

Definition bounded_lattice_to_lattice X : bounded_lattice X → lattice X := pr1.
Coercion bounded_lattice_to_lattice : bounded_lattice >-> lattice.

Definition Lbot {X : hSet} (is : bounded_lattice X) : X := pr1 (pr2 is).
Definition Ltop {X : hSet} (is : bounded_lattice X) : X := pr1 (pr2 (pr2 is)).

Section bounded_lattice_pty.

Context {X : hSet} (l : bounded_lattice X).

Definition islunit_Lmax_Lbot : islunit (Lmax l) (Lbot l) :=
  pr1 (pr2 (pr2 (pr2 l))).

Definition islunit_Lmin_Ltop : islunit (Lmin l) (Ltop l) :=
  pr2 (pr2 (pr2 (pr2 l))).

Lemma Lmin_Lbot (x : X) : Lmin l (Lbot l) x = Lbot l.
Proof.
now rewrite <- (islunit_Lmax_Lbot x), Lmin_absorb.
Qed.

Lemma Lmax_Ltop (x : X) : Lmax l (Ltop l) x = Ltop l.
Proof.
now rewrite <- (islunit_Lmin_Ltop x), Lmax_absorb.
Qed.

End bounded_lattice_pty.

Definition hProp_bounded_lattice : bounded_lattice (hProp,,isasethProp).
Proof.
use make_bounded_lattice.
- exact hProp_lattice.
- exact hfalse.
- exact htrue.
- split.
  + intros P; apply hfalse_hdisj.
  + intros P; apply htrue_hconj.
Defined.
