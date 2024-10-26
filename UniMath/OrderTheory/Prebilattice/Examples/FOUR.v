(** The pre-bilattice FOUR *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)
Require Import UniMath.OrderTheory.Prebilattice.Prebilattice.
Require Import UniMath.OrderTheory.Prebilattice.Product.
Require Import UniMath.OrderTheory.Prebilattice.Interlaced.
Require Import UniMath.OrderTheory.Prebilattice.Distributive.
Require Import UniMath.OrderTheory.Lattice.Examples.Bool.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Bool.

Definition FOUR := make_bounded_prod_prebilattice boolset_bounded_lattice boolset_bounded_lattice .

Lemma is_interlaced_FOUR : is_interlaced FOUR .
Proof.
  exact (prod_prebilattices_are_interlaced FOUR) .
Defined.

Definition is_distributive_FOUR : is_distributive_prebilattice FOUR .
Proof .
  do 9 (try use make_dirprod); unfold consensus, gullibility, meet, join, tlattice, klattice, Lattice.Lmin, Lattice.Lmax; cbn; unfold prod_prebilattice_consensus, prod_prebilattice_gullibility, prod_prebilattice_meet, prod_prebilattice_join; intros x y z; induction (pr1 x), (pr2 x), (pr1 y), (pr2 y), (pr1 z), (pr2 z); trivial.
Defined.
