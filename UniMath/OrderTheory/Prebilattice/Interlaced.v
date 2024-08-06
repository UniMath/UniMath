(** Interlaced pre-bilattice *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)

(**
 In interlaced pre-bilattices, the two lattices
 are linked via monotonicity of the operators of each lattice
 with respect to the other lattice.
**)
Require Import UniMath.OrderTheory.Prebilattice.Prebilattice.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Algebra.BinaryOperations.

Section definition .
  Definition interlacing {X : hSet} (op : binop X) (R : hrel X) :=
    ∏ x y z : X, R x y -> R (op x z) (op y z).

  Lemma isaprop_interlacing {X : hSet} (op : binop X) (R : hrel X) : isaprop (interlacing op R).
  Proof.
    do 4 (use impred; intro).
    use propproperty.
  Defined.

  Definition is_interlaced {X : hSet} (b : prebilattice X) : UU :=
    interlacing (consensus b) (tle b)
                ×
                interlacing (gullibility b) (tle b)
                ×
                interlacing (meet b) (kle b)
                ×
                interlacing (join b) (kle b).

  Lemma isaprop_is_interlaced {X : hSet} {b : prebilattice X} : isaprop (is_interlaced b).
  Proof.
    do 3 (try use (isapropdirprod)); use isaprop_interlacing.
  Defined.

  Definition interlaced_prebilattice (X : hSet) :=
    ∑ b : prebilattice X,  is_interlaced b.

  Definition make_interlaced_prebilattice {X : hSet} {b : prebilattice X} (is : is_interlaced b) : interlaced_prebilattice X := b,,is.

  Definition interlaced_prebilattice_to_prebilattice {X : hSet} (b: interlaced_prebilattice X) : prebilattice X := pr1 b.
  Coercion interlaced_prebilattice_to_prebilattice : interlaced_prebilattice >-> prebilattice .
End definition.

Section equalities.
  Definition interlaced_prebilattice_eq {X : hSet} (b1 : interlaced_prebilattice X) (b2 : interlaced_prebilattice X) (m : meet b1 ~ meet b2) (j : join b1 ~ join b2) (c : consensus b1 ~ consensus b2) (g : gullibility b1 ~ gullibility b2): b1 = b2.
  Proof.
    use total2_paths_f.
    - use (prebilattice_eq b1 b2 m j c g).
    - apply isaprop_is_interlaced.
  Defined.

  Definition interlaced_prebilattice_transportf {X1 X2 : hSet} (b1 : interlaced_prebilattice X1) (b2 : interlaced_prebilattice X2) (p : X1 = X2)
             (m : meet (transportf interlaced_prebilattice p b1) ~ meet b2)
             (j : join (transportf interlaced_prebilattice p b1) ~ join b2)
             (c : consensus (transportf interlaced_prebilattice p b1) ~ consensus b2)
             (g : gullibility (transportf interlaced_prebilattice p b1) ~ gullibility b2)
    : transportf interlaced_prebilattice p b1 = b2.
  Proof.
    use total2_paths_f.
    - unfold interlaced_prebilattice.
      rewrite (pr1_transportf p b1).
      use prebilattice_transportf; [set (i := m) | set (i := j) | set (i := c) | set (i := g)];
        use (homotcomp _ i);
        induction p;
        use homotrefl.
    - apply isaprop_is_interlaced.
  Defined.
End equalities.

Section properties.
  Lemma interlacing_consensus_t {X : hSet} (b : interlaced_prebilattice X) : interlacing (consensus b) (tle b).
  Proof .
    exact (pr12 b) .
  Defined.
  Lemma interlacing_gullibility_t {X : hSet} (b : interlaced_prebilattice X) : interlacing (gullibility b) (tle b).
  Proof.
    exact (pr122 b) .
  Defined.
  Lemma interlacing_meet_k {X : hSet} (b : interlaced_prebilattice X) :  interlacing (meet b) (kle b) .
  Proof.
    exact (pr1 (pr2 (pr2 (pr2 b)))) .
  Defined.
  Lemma interlacing_join_k {X : hSet} (b : interlaced_prebilattice X) :  interlacing (join b) (kle b) .
  Proof.
    exact (pr2 (pr2 (pr2 (pr2 b)))) .
  Defined.

  Definition double_interlacing {X : hSet} {op : binop X} {R : hrel X} (i : interlacing op R) (a : istrans R) (c : iscomm op) {x y z w : X} (p : R x y) (q : R z w) : R (op x z) (op y w).
  Proof.
    use (a (op x z) (op y z)).
    - use i. exact p.
    - rewrite (c y z), (c y w). use i . exact q.
  Defined.

  Lemma double_interlacing_gullibility_t {X : hSet} {b : interlaced_prebilattice X} {x y z w : X} (p : tle b x y) (q : tle b z w) : tle b (gullibility b x z) (gullibility b y w) .
  Proof.
    exact (double_interlacing (interlacing_gullibility_t _) (istrans_Lle (tlattice _)) (iscomm_Lmax (klattice _)) p q) .
  Defined.
  Lemma double_interlacing_consensus_t {X : hSet} {b : interlaced_prebilattice X} {x y z w : X} (p : tle b x y) (q : tle b z w) : tle b (consensus b x z) (consensus b y w) .
  Proof.
    exact (double_interlacing (interlacing_consensus_t _) (istrans_Lle (tlattice _)) (iscomm_Lmin (klattice _)) p q) .
  Defined.
  Lemma double_interlacing_meet_k {X : hSet} {b : interlaced_prebilattice X} {x y z w : X} (p : kle b x y) (q : kle b z w) : kle b (meet b x z) (meet b y w) .
  Proof.
    exact (double_interlacing (interlacing_meet_k _) (istrans_Lle (klattice _)) (iscomm_Lmin (tlattice _)) p q).
  Defined.
  Lemma double_interlacing_join_k {X : hSet} {b : interlaced_prebilattice X} {x y z w : X} (p : kle b x y) (q : kle b z w) : kle b (join b x z) (join b y w) .
  Proof.
    exact (double_interlacing (interlacing_join_k _) (istrans_Lle (klattice _)) (iscomm_Lmax (tlattice _)) p q).
  Defined.

  Lemma top_interlacing_gullibility_t {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : tle b x z) (q : tle b y z) : tle b (gullibility b x y) z.
  Proof.
    rewrite <- (Lmax_id (klattice b) z).
    use (double_interlacing_gullibility_t p q).
  Defined.
  Lemma top_interlacing_consensus_t {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : tle b x z) (q : tle b y z) : tle b (consensus b x y) z.
  Proof.
    rewrite <- (Lmin_id (klattice b) z).
    use (double_interlacing_consensus_t p q).
  Defined.
  Lemma top_interlacing_join_k {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : kle b x z) (q : kle b y z) : kle b (join b x y) z.
  Proof.
    rewrite <- (Lmax_id (tlattice b) z).
    use (double_interlacing_join_k p q).
  Defined.
  Lemma top_interlacing_meet_k {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : kle b x z) (q : kle b y z) : kle b (meet b x y) z.
  Proof.
    rewrite <- (Lmin_id (tlattice b) z).
    use (double_interlacing_meet_k p q).
  Defined.

  Lemma bottom_interlacing_join_k {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : kle b z x) (q : kle b z y) : kle b z (join b x y).
  Proof.
    rewrite <- (Lmax_id (tlattice b) z).
    use (double_interlacing_join_k p q).
  Defined.
  Lemma bottom_interlacing_meet_k {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : kle b z x) (q : kle b z y) : kle b z (meet b x y).
  Proof.
    rewrite <- (Lmin_id (tlattice b) z).
    use (double_interlacing_meet_k p q).
  Defined.
  Lemma bottom_interlacing_gullibility_t {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : tle b z x) (q : tle b z y) : tle b z (gullibility b x y).
  Proof.
    rewrite <- (Lmax_id (klattice b) z).
    use (double_interlacing_gullibility_t p q).
  Defined.
  Lemma bottom_interlacing_consensus_t {X : hSet} {b : interlaced_prebilattice X} {x y z : X} (p : tle b z x) (q : tle b z y) : tle b z (consensus b x y).
  Proof.
    rewrite <- (Lmin_id (klattice b) z).
    use (double_interlacing_consensus_t p q).
  Defined.

  Lemma dual_prebilattice_is_interlaced {X : hSet} (b : interlaced_prebilattice X) : is_interlaced (dual_prebilattice b).
  Proof.
    destruct b as [? [? [? [? ?]]]] . do 3 (try split); assumption .
  Defined.

  Lemma opp_prebilattice_is_interlaced {X : hSet} (b : interlaced_prebilattice X) : is_interlaced (opp_prebilattice b).
  Proof.
    do 3 (try split); intros ? ? ? H;
    [set (i := (interlacing_gullibility_t b)) | set (i := interlacing_consensus_t b) | set (i := interlacing_join_k b) | set (i := interlacing_meet_k b)];
    use (Lmax_le_eq_l _ _ _ (i _ _ _ (Lmax_le_eq_l _ _ _ H))).
  Defined.

  Lemma t_opp_prebilattice_is_interlaced {X : hSet} (b : interlaced_prebilattice X) : is_interlaced (t_opp_prebilattice b).
  Proof.
    do 3 (try split); intros ? ? ? H.
    - use (Lmax_le_eq_l _ _ _ (interlacing_consensus_t _ _ _ _ (Lmax_le_eq_l _ _ _ H))).
    - use (Lmax_le_eq_l _ _ _ (interlacing_gullibility_t _ _ _ _ (Lmax_le_eq_l _ _ _ H))).
    - use (interlacing_join_k _ _ _ _ H).
    - use (interlacing_meet_k _ _ _ _ H).
  Defined.

  Lemma k_opp_prebilattice_is_interlaced {X : hSet} (b : interlaced_prebilattice X) : is_interlaced (k_opp_prebilattice b).
  Proof.
    destruct (t_opp_prebilattice_is_interlaced (make_interlaced_prebilattice (dual_prebilattice_is_interlaced b))) as [? [? [? ?]]].
    do 3 (try split); assumption.
  Defined.

  Lemma interlaced_leqt_leqk_leqkmeet {X : hSet} : ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> kle b x (meet b y x).
  Proof.
    intros ? x y [? [p1 p2]].
    set (w := (meet _ y x)); rewrite <- (Lmin_le_eq_r _ _ _ p1).
    use (interlacing_meet_k _ _ _ _ p2).
  Defined.

  Lemma interlaced_leqk_leqt_leqtconsensus {X:hSet}: ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> tle b x (consensus b y x).
  Proof.
    intro b'.
    use (interlaced_leqt_leqk_leqkmeet (make_interlaced_prebilattice (dual_prebilattice_is_interlaced b'))).
  Defined.

  Lemma interlaced_leqk_geqt_geqtconsensus {X:hSet}: ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, kle b x r × tle b y r) -> tle b (consensus b y x) x.
  Proof.
    intros ? x y [? [p1 p2]].
    set (w := (consensus _ y x)); rewrite <- (Lmin_le_eq_r _ _ _ p1).
    use (interlacing_consensus_t _ _ _ _ p2).
  Defined.

  Lemma interlaced_leqt_leqk_leqtconsensus {X : hSet} : ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, tle b x r × kle b r y) -> tle b x (consensus b y x).
  Proof.
    intros b' ? ? [? [p1 p2]].
    set (pp := interlaced_leqt_leqk_leqkmeet _ _ _ (_,,p1,,p2)).
    rewrite (iscomm_meet) in pp.
    use (interlaced_leqk_leqt_leqtconsensus _ _ _ (_,, pp,, Lmin_le_r (tlattice b') _ _)).
  Defined.

  Lemma interlaced_geqt_leqk_geqtconsensus {X : hSet} : ∏ (b : interlaced_prebilattice X) (x y : X), (∑ r : X, tle b r x × kle b r y) -> tle b (consensus b y x) x.
  Proof.
    intros b x y [r [p1 p2]].
    assert (p1' :  tle (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b)) x r).
    {
      rewrite <- p1, iscomm_Lmin.
      use Lmax_absorb.
    }
    set (t := consensus b y x).
    assert (p : Lmax (tlattice b) t x = x).
    {
      rewrite iscomm_Lmax.
      exact (interlaced_leqt_leqk_leqtconsensus (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b)) x y (r,,p1',,p2)).
    }
    rewrite <- p.
    use Lmin_absorb.
  Defined.

  Lemma interlaced_geqt_geqk_geqkjoin {X: hSet} :  ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, tle b r x × kle b y r) -> kle b (join b y x) x .
  Proof.
    intros b' ? ? [? [p1 p2]].
    set (bop := make_interlaced_prebilattice (opp_prebilattice_is_interlaced b')).
    set (H := interlaced_leqt_leqk_leqkmeet bop _ _ (_,,(Lmax_le_eq_l _ _ _ p1),, (Lmax_le_eq_l _ _ _ p2))).
    use (Lmax_le_eq_l _ _ _ H).
  Defined.

  Lemma interlaced_leqk_leqt_leqkmeet {X : hSet} :  ∏ (b : interlaced_prebilattice X) (x y : X) , (∑ r : X, kle b x r × tle b r y) -> kle b x (meet b y x) .
  Proof .
    intro b'.
    use (interlaced_leqt_leqk_leqtconsensus (make_interlaced_prebilattice (dual_prebilattice_is_interlaced b'))).
  Defined.
End properties.
