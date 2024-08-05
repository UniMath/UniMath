(** Pre-bilattice *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)
(**
  Pre-bilattices are structures
  comprising two lattice structures over the same set.

  Usually, the first lattice is called the 'truth' lattice
  (hence tlattice below) with operators 'meet' and 'join',
  while the second lattice is called the 'knowledge' lattce
  (hence klattice below) with operators 'conensus' and 'gulliblity'.
*)
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.

Section Def .
  Definition prebilattice (X : hSet) := lattice X × lattice X .

  Definition prebilattice_carrier {X : hSet} (b : prebilattice X) := X.
  Coercion prebilattice_carrier : prebilattice >-> hSet.

  Definition make_prebilattice {X : hSet} (tLattice kLattice: lattice X) : prebilattice X := tLattice,, kLattice.

  Definition tlattice {X : hSet} (b : prebilattice X) : lattice X := pr1 b .
  Definition klattice {X : hSet} (b : prebilattice X) : lattice X := pr2 b .

  Definition dual_prebilattice {X : hSet} (b : prebilattice X) := make_prebilattice (klattice b)  (tlattice b) .
  Definition t_opp_prebilattice {X : hSet} (b : prebilattice X) := make_prebilattice (dual_lattice (tlattice b)) (klattice b) .
  Definition k_opp_prebilattice {X : hSet} (b : prebilattice X) := dual_prebilattice (t_opp_prebilattice (dual_prebilattice b)).
  Definition opp_prebilattice {X : hSet} (b : prebilattice X) := make_prebilattice (dual_lattice (tlattice b)) (dual_lattice (klattice b)) .

  Definition meet {X : hSet} (b : prebilattice X) : binop X := Lmin (tlattice b) .
  Definition join {X: hSet} (b : prebilattice X) : binop X := Lmax (tlattice b) .
  Definition consensus {X : hSet} (b : prebilattice X) : binop X := Lmin (klattice b) .
  Definition gullibility {X : hSet} (b : prebilattice X) : binop X := Lmax (klattice b) .

  Lemma isaset_prebilattice (X : hSet) : isaset (prebilattice X) .
  Proof.
    exact(isaset_dirprod (isaset_lattice X) (isaset_lattice X)).
  Defined.

  Definition prebilattice_transportf {X1 X2 : hSet} (b1 : prebilattice X1) (b2 : prebilattice X2) (p : X1 = X2)
             (m : meet (transportf prebilattice p b1) ~ meet b2)
             (j : join (transportf prebilattice p b1) ~ join b2)
             (c : consensus (transportf prebilattice p b1) ~ consensus b2)
             (g : gullibility (transportf prebilattice p b1) ~ gullibility b2)
    : transportf prebilattice p b1 = b2.
  Proof.
    use dirprodeq.
    - use total2_paths_f.
      -- use weqfunextsec. use m.
      -- use total2_paths_f.
         --- use weqfunextsec.
             rewrite transportf_total2_const.
             use j.
         --- apply isaprop_islatticeop.
    - use total2_paths_f.
      -- use weqfunextsec. use c.
      -- use total2_paths_f.
         --- use weqfunextsec.
             rewrite transportf_total2_const.
             use g.
         --- apply isaprop_islatticeop.
  Defined.

  Definition prebilattice_eq {X : hSet} (b1 : prebilattice X) (b2 : prebilattice X) (m : meet b1 ~ meet b2) (j : join b1 ~ join b2) (c : consensus b1 ~ consensus b2) (g : gullibility b1 ~ gullibility b2): b1 = b2.
  Proof.
    use (@prebilattice_transportf X X b1 b2 (idpath X)); now rewrite idpath_transportf.
  Defined.
End Def.

Section Properties.
  Lemma isassoc_consensus {X : hSet} (b : prebilattice X) : isassoc (consensus b).
  Proof.
    exact (isassoc_Lmin (klattice b)) .
  Defined.
  Lemma isassoc_join {X : hSet} (b : prebilattice X) : isassoc (join b) .
  Proof.
    exact (isassoc_Lmax (tlattice b)) .
  Defined.
  Lemma isassoc_meet {X : hSet} (b : prebilattice X) : isassoc (meet b) .
  Proof.
    exact (isassoc_Lmin (tlattice b)) .
  Defined.
  Lemma iscomm_consensus {X : hSet} (b : prebilattice X) : iscomm (consensus b) .
  Proof.
    exact (iscomm_Lmin (klattice b)) .
  Defined.
  Lemma iscomm_gullibility {X : hSet} (b : prebilattice X) : iscomm (gullibility b) .
  Proof.
    exact (iscomm_Lmax (klattice b)) .
  Defined.
  Lemma iscomm_meet {X : hSet} (b : prebilattice X) : iscomm (meet b) .
  Proof.
    exact (iscomm_Lmin (tlattice b)) .
  Defined.
  Lemma iscomm_join {X : hSet} (b : prebilattice X) : iscomm (join b) .
  Proof.
    exact (iscomm_Lmax (tlattice b)) .
  Defined.
  Lemma join_id {X : hSet} (b : prebilattice X) (x : X) : join b x x = x .
  Proof.
    exact (Lmax_id (tlattice b) x).
  Defined.
  Lemma meet_id {X : hSet} (b : prebilattice X) (x : X) : meet b x x = x .
  Proof.
    exact (Lmin_id (tlattice b) x).
  Defined.

  Lemma consensus_gullibility_absorb {X : hSet} (b : prebilattice X) (x y : X) : consensus b x (gullibility b x y) = x .
  Proof.
    exact (Lmin_absorb (klattice b) x y).
  Defined.
  Lemma gullibility_consensus_absorb {X : hSet} (b : prebilattice X) (x y : X) : gullibility b x (consensus b x y) = x .
  Proof.
    exact (Lmax_absorb (klattice b) x y).
  Defined.
  Lemma meet_join_absorb {X : hSet} (b : prebilattice X) (x y : X) : meet b x (join b x y) = x .
  Proof.
    exact (Lmin_absorb (tlattice b) x y).
  Defined.
  Lemma join_meet_absorb {X : hSet} (b : prebilattice X) (x y : X) : join b x (meet b x y) = x .
  Proof.
    exact (Lmax_absorb (tlattice b) x y).
  Defined.

  Definition tle {X : hSet} (b : prebilattice X) : hrel X := Lle (tlattice b).
  Definition kle {X : hSet} (b : prebilattice X) : hrel X := Lle (klattice b).
  Definition tge {X : hSet} (b : prebilattice X) : hrel X := Lge (tlattice b).
  Definition kge {X : hSet} (b : prebilattice X) : hrel X := Lge (klattice b).

  Lemma istrans_tle {X : hSet} (b : prebilattice X) : istrans (tle b) .
  Proof.
    exact (istrans_Lle (tlattice b)).
  Defined.
  Lemma istrans_kle {X : hSet} (b : prebilattice X) : istrans (kle b) .
  Proof.
    exact (istrans_Lle (klattice b)).
  Defined.
End Properties .

Section Bounded .
  Definition bounded_prebilattice (X : hSet) :=
    bounded_lattice X × bounded_lattice X.

  Definition make_bounded_prebilattice {X : hSet} (tLattice kLattice : bounded_lattice X) : bounded_prebilattice X := tLattice,, kLattice.

  Definition bounded_prebilattice_to_prebilattice X (b : bounded_prebilattice X) : prebilattice X := make_prebilattice (pr1 b) (pr2 b) .
  Coercion bounded_prebilattice_to_prebilattice : bounded_prebilattice >-> prebilattice.

  Definition fls {X : hSet} (b : bounded_prebilattice X) : X :=  Lbot (pr1 b).
  Definition tru {X : hSet} (b : bounded_prebilattice X) : X :=  Ltop (pr1 b).
  Definition bot {X: hSet} (b : bounded_prebilattice X) : X :=  Lbot (pr2 b) .
  Definition top {X: hSet} (b : bounded_prebilattice X) : X :=  Ltop (pr2 b) .
End Bounded .
