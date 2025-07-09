(** Interlaced pre-bilattice *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)

(**
 Distributive pre-bilattices are generalisations of distributive lattices.
 Every distributive pre-bilattice is also interlaced.
 **)
Require Import UniMath.OrderTheory.Prebilattice.Prebilattice.
Require Import UniMath.OrderTheory.Prebilattice.Interlaced.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Distributive.

Section Def.
  Definition is_distributive_prebilattice {X : hSet} (b : prebilattice X) :=
    isldistr (gullibility b) (consensus b)
             × isldistr (join b) (meet b)
             × isldistr (consensus b) (meet b)
             × isldistr (meet b) (consensus b)
             × isldistr (consensus b) (join b)
             × isldistr (join b) (consensus b)
             × isldistr (gullibility b) (meet b)
             × isldistr (meet b) (gullibility b)
             × isldistr (gullibility b) (join b)
             × isldistr (join b) (gullibility b)
  .

  Lemma isaprop_is_distributive {X : hSet} {b : prebilattice X} : isaprop (is_distributive_prebilattice b).
  Proof.
    do 9 (try use (isapropdirprod)); use isapropisldistr.
  Defined.

  Definition distributive_prebilattice (X : hSet) :=
    ∑ b : prebilattice X, is_distributive_prebilattice b.

  Definition distributive_prebilattices_to_prebilattices {X : hSet} (b : distributive_prebilattice X) : prebilattice X := pr1 b.

  Coercion distributive_prebilattices_to_prebilattices : distributive_prebilattice >-> prebilattice .

  Definition make_distributive_prebilattice {X : hSet} {b : prebilattice X} (is : is_distributive_prebilattice b) : distributive_prebilattice X := b,,is .
End Def.

Section Properties.
  Lemma is_distributive_klattice {X : hSet}  (b : distributive_prebilattice X) : is_distributive (klattice b).
  Proof.
    intros x y z.
    exact(pr12 b y z x).
  Defined.
  Lemma is_distributive_tlattice {X : hSet}  (b : distributive_prebilattice X) : is_distributive (tlattice b).
  Proof.
    intros x y z.
    exact(pr122 b y z x).
  Defined.
  Lemma ldistr_gullibility_consensus {X : hSet} (b : distributive_prebilattice X) : isldistr (gullibility b) (consensus b).
  Proof.
    exact (pr12 b).
  Defined.
  Lemma ldistr_consensus_gullibility {X : hSet} (b : distributive_prebilattice X)  : isldistr (consensus b) (gullibility b) .
  Proof.
    exact (distrlattice_Lmin_ldistr (make_distributive_lattice (is_distributive_klattice b))) .
  Defined.
  Lemma rdistr_gullibility_consensus {X : hSet} (b : distributive_prebilattice X) : isrdistr (gullibility b) (consensus b) .
  Proof.
    exact (distrlattice_Lmax_rdistr (make_distributive_lattice (is_distributive_klattice b))) .
  Defined.
  Lemma rdistr_consensus_gullibility {X : hSet} (b : distributive_prebilattice X): isrdistr (consensus b) (gullibility b) .
  Proof.
    exact (distrlattice_Lmin_rdistr (make_distributive_lattice (is_distributive_klattice b))).
  Defined.
  Lemma ldistr_join_meet {X : hSet} (b : distributive_prebilattice X) : isldistr (join b) (meet b) .
  Proof.
    exact (pr122 b).
  Defined.
  Lemma ldistr_meet_join {X : hSet} (b : distributive_prebilattice X) : isldistr (meet b) (join b) .
  Proof.
    exact (distrlattice_Lmin_ldistr (make_distributive_lattice (is_distributive_tlattice b))).
  Defined.
  Lemma rdistr_meet_join {X : hSet} (b : distributive_prebilattice X) : isrdistr (meet b) (join b) .
  Proof.
    exact ((distrlattice_Lmin_rdistr (make_distributive_lattice (is_distributive_tlattice b)))).
  Defined.
  Lemma rdistr_join_meet {X : hSet} (b : distributive_prebilattice X) : isrdistr (join b) (meet b) .
  Proof.
    exact ((distrlattice_Lmax_rdistr (make_distributive_lattice (is_distributive_tlattice b)))).
  Defined.
  Lemma ldistr_consensus_meet {X : hSet} (b : distributive_prebilattice X) : isldistr (consensus b) (meet b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 b)))).
  Defined.
  Lemma rdistr_consensus_meet {X : hSet} (b : distributive_prebilattice X) : isrdistr (consensus b) (meet b) .
  Proof.
    exact (weqldistrrdistr (consensus b) (meet b) (iscomm_meet b) (ldistr_consensus_meet b)) .
  Defined.
  Lemma ldistr_meet_consensus {X : hSet} (b : distributive_prebilattice X) : isldistr (meet b) (consensus b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 b))))) .
  Defined.
  Lemma rdistr_meet_consensus {X : hSet} (b : distributive_prebilattice X) : isrdistr (meet b) (consensus b) .
  Proof.
    exact (weqldistrrdistr (meet b) (consensus b) (iscomm_consensus b) (ldistr_meet_consensus b)).
  Defined.
  Lemma ldistr_consensus_join {X : hSet} (b : distributive_prebilattice X) : isldistr (consensus b) (join b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))) .
  Defined.
  Lemma rdistr_consensus_join {X : hSet} (b : distributive_prebilattice X) : isrdistr (consensus b) (join b) .
  Proof.
    exact (weqldistrrdistr (consensus b) (join b) (iscomm_join b) (ldistr_consensus_join b)).
  Defined.
  Lemma ldistr_join_consensus {X : hSet} (b : distributive_prebilattice X) : isldistr (join b) (consensus b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b))))))) .
  Defined.
  Lemma rdistr_join_consensus {X : hSet} (b : distributive_prebilattice X) : isrdistr (join b) (consensus b) .
  Proof.
    exact (weqldistrrdistr (join b) (consensus b) (iscomm_consensus b) (ldistr_join_consensus b)) .
  Defined.
  Lemma ldistr_gullibility_meet {X : hSet} (b : distributive_prebilattice X) : isldistr (gullibility b) (meet b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))))) .
  Defined.
  Lemma rdistr_gullibility_meet {X : hSet} (b : distributive_prebilattice X) : isrdistr (gullibility b) (meet b) .
  Proof.
    exact (weqldistrrdistr (gullibility b) (meet b) (iscomm_meet b) (ldistr_gullibility_meet b)) .
  Defined.
  Lemma ldistr_meet_gullibility {X : hSet} (b : distributive_prebilattice X) : isldistr (meet b) (gullibility b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b))))))))) .
  Defined.
  Lemma rdistr_meet_gullibility {X : hSet} (b : distributive_prebilattice X) : isrdistr (meet b) (gullibility b) .
  Proof.
    exact (weqldistrrdistr (meet b) (gullibility b) (iscomm_gullibility b) (ldistr_meet_gullibility b)) .
  Defined.
  Lemma ldistr_gullibility_join {X : hSet} (b : distributive_prebilattice X) : isldistr (gullibility b) (join b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))))))) .
  Defined.
  Lemma rdistr_gullibility_join {X : hSet} (b : distributive_prebilattice X) : isrdistr (gullibility b) (join b) .
  Proof.
    exact (weqldistrrdistr (gullibility b) (join b) (iscomm_join b) (ldistr_gullibility_join b)) .
  Defined.
  Lemma ldistr_join_gullibility {X : hSet} (b : distributive_prebilattice X) : isldistr (join b) (gullibility b) .
  Proof.
    exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 b)))))))))) .
  Defined.
  Lemma rdistr_join_gullibility {X : hSet} (b : distributive_prebilattice X) : isrdistr (join b) (gullibility b) .
  Proof.
    exact (weqldistrrdistr (join b) (gullibility b) (iscomm_gullibility b) (ldistr_join_gullibility b)) .
  Defined.

  Proposition distributive_prebilattices_are_interlaced_prebilattices {X : hSet} (b : distributive_prebilattice X) : is_interlaced b .
  Proof.
    do 3 (try split); intros x y z H.
    - rewrite (iscomm_consensus _ x z), (iscomm_consensus _ y z).
      set(d := ldistr_meet_consensus b x y z). unfold meet in d. cbn.
      rewrite <- d,  H. reflexivity.
    - rewrite (iscomm_gullibility _ x z), (iscomm_gullibility _ y z).
      set (d := ldistr_meet_gullibility b x y z). unfold meet in d. cbn.
      rewrite <- d,  H; reflexivity.
    - rewrite (iscomm_meet _ x z), (iscomm_meet _ y z).
      set (d := (ldistr_consensus_meet b x y z)). unfold consensus in d. cbn.
      rewrite <- d , H;  reflexivity.
    - rewrite (iscomm_join _ x z), (iscomm_join _ y z).
      set (d := ldistr_consensus_join b x y z). unfold consensus in d. cbn.
      rewrite <- d, H; reflexivity .
  Defined.

  Definition distributive_prebilattices_to_interlaced_prebilattices {X : hSet} (b : distributive_prebilattice X) : interlaced_prebilattice X :=
    make_interlaced_prebilattice (distributive_prebilattices_are_interlaced_prebilattices b).

  Coercion distributive_prebilattices_to_interlaced_prebilattices : distributive_prebilattice >-> interlaced_prebilattice .
End Properties.
