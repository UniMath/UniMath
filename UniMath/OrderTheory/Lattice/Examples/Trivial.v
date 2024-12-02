(**********************************************************************************************

 The trivial complete Heyting algebra

 The unit type forms a complete Heyting algebra in a trivial way. All operations are constant
 and the laws hold because the unit type is a proposition.

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Heyting.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.

Definition unit_lattice
  : lattice unitset.
Proof.
  use make_lattice.
  - exact (λ _ _, tt).
  - exact (λ _ _, tt).
  - abstract
      (repeat split ; intro ; intros ; apply isapropunit).
Defined.

Definition unit_bounded_lattice
  : bounded_lattice unitset.
Proof.
  use make_bounded_lattice.
  - exact unit_lattice.
  - exact tt.
  - exact tt.
  - abstract
      (split ; intro ; intros ; apply isapropunit).
Defined.

Definition unit_complete_lattice
  : is_complete_lattice unit_bounded_lattice.
Proof.
  intros I f.
  refine (tt ,, _).
  abstract
    (split ; intro ; intros ; apply isapropunit).
Defined.

Definition unit_lattice_exponential
  : exponential unit_bounded_lattice.
Proof.
  use make_exponential.
  - exact (λ _ _, tt).
  - abstract
      (intros ; split ; intro ; intros ; apply isapropunit).
Defined.

Definition unit_cha
  : complete_heyting_algebra.
Proof.
  use make_complete_heyting_algebra.
  - exact unitset.
  - exact unit_bounded_lattice.
  - exact unit_complete_lattice.
  - exact unit_lattice_exponential.
Defined.
