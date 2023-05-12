(** * Lattice structure on [boolset] *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Bool.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Distributive.
Require Import UniMath.Algebra.Lattice.Complement.
Require Import UniMath.Algebra.Lattice.Boolean.

Lemma boolset_lattice : lattice boolset.
Proof.
  use make_lattice.
  - exact andb. (** [Lmin] *)
  - exact orb. (** [Lmax] *)
  - (** TODO: constructor for this *)
    apply make_dirprod; [apply make_dirprod|apply make_dirprod; [apply make_dirprod|apply make_dirprod]].
    + intros ? ? ?; apply andb_is_associative.
    + intros ? ?; apply andb_is_commutative.
    + intros ? ? ?; apply orb_is_associative.
    + intros ? ?; apply orb_is_commutative.
    + intros b1 b2; abstract (induction b1, b2; reflexivity).
    + intros b1 b2; abstract (induction b1, b2; reflexivity).
Defined.

Lemma boolset_lattice_is_bounded :
  bounded_latticeop boolset_lattice false true.
Proof.
  use make_dirprod; compute; reflexivity.
Qed.

Lemma boolset_lattice_is_complemented :
  complemented_structure (make_bounded_lattice boolset_lattice_is_bounded).
Proof.
  intros b.
  exists (negb b).
  use make_dirprod.
  - abstract (induction b; reflexivity).
  - abstract (induction b; reflexivity).
Qed.

Definition boolset_bounded_lattice : bounded_lattice boolset.
Proof.
  use make_bounded_lattice.
  - exact boolset_lattice.
  - exact false.
  - exact true.
  - exact boolset_lattice_is_bounded.
Defined.

Lemma boolset_lattice_is_distributive : is_distributive boolset_lattice.
Proof.
  intros b1 b2 b3; induction b1, b2, b3; reflexivity.
Qed.

Definition subset_lattice_is_boolean : is_boolean boolset_bounded_lattice.
Proof.
  use make_is_boolean.
  - apply boolset_lattice_is_distributive.
  - apply boolset_lattice_is_complemented.
Qed.