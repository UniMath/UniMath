(** Product pre-bilattice *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)

(**
  Given two lattices, it is possible to (uniquely)
  construct a product pre-bilattice.

  Product pre-bilattices are always interlaced.
  The opposite is called the 'representation theorem'.
**)
Require Import UniMath.OrderTheory.Prebilattice.Prebilattice.
Require Import UniMath.OrderTheory.Prebilattice.Interlaced.
Require Import UniMath.OrderTheory.Prebilattice.PrebilatticeDisplayedCat.
Require Import UniMath.MoreFoundations.Equivalences.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.

Section definition .
  Definition prod_prebilattice_carrier (X1 X2 : hSet) := setdirprod X1 X2 .

  Definition prod_prebilattice_meet {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_prebilattice_carrier X1 X2) :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .
  Definition prod_prebilattice_join  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_prebilattice_carrier X1 X2) :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition prod_prebilattice_consensus  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_prebilattice_carrier X1 X2) :=
    λ x y, (((Lmin l1) (pr1 x) (pr1 y)),, (Lmin l2) (pr2 x) (pr2 y)) .
  Definition prod_prebilattice_gullibility  {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : binop (prod_prebilattice_carrier X1 X2) :=
    λ x y, (((Lmax l1) (pr1 x) (pr1 y)),, (Lmax l2) (pr2 x) (pr2 y)) .

  Definition prod_prebilattice (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) := (islatticeop (prod_prebilattice_meet l1 l2) (prod_prebilattice_join l1 l2)) × (islatticeop (prod_prebilattice_consensus l1 l2) (prod_prebilattice_gullibility l1 l2)).

  Definition islatticeop_prod_t {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : islatticeop (prod_prebilattice_meet l1 l2) (prod_prebilattice_join l1 l2) .
  Proof .
    do 4 (try use make_dirprod).
    - intros a b c; induction a, b, c. use dirprod_paths; [use isassoc_Lmin | use isassoc_Lmax].
    - intros a b; induction a, b. use dirprod_paths; [use iscomm_Lmin | use iscomm_Lmax] .
    - intros a b c; induction a, b, c. use dirprod_paths; [use isassoc_Lmax | use isassoc_Lmin] .
    - intros a b; induction a, b. use dirprod_paths; [use iscomm_Lmax | use iscomm_Lmin ].
    - intros a b; induction a, b. use dirprod_paths; [use Lmin_absorb | use Lmax_absorb ].
    - intros a b; induction a, b. use dirprod_paths; [use Lmax_absorb | use Lmin_absorb] .
  Defined .

  Definition islatticeop_prod_k {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : islatticeop (prod_prebilattice_consensus l1 l2) (prod_prebilattice_gullibility l1 l2) .
  Proof .
    do 4 (try use make_dirprod).
    - intros a b c; induction a, b, c. use dirprod_paths; use isassoc_Lmin.
    - intros a b; induction a, b. use dirprod_paths; use iscomm_Lmin.
    - intros a b c; induction a, b, c. use dirprod_paths; use isassoc_Lmax .
    - intros a b; induction a, b. use dirprod_paths; use iscomm_Lmax .
    - intros a b; induction a, b. use dirprod_paths; use Lmin_absorb .
    - intros a b; induction a, b. use dirprod_paths; use Lmax_absorb .
  Defined .

  Definition make_prod_prebilattice {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : prod_prebilattice X1 X2 l1 l2 :=
    islatticeop_prod_t l1 l2,,islatticeop_prod_k l1 l2.

  Lemma iscontr_prod_prebilattice {X1 X2 : hSet} (l1 : lattice X1) (l2 : lattice X2) : iscontr (prod_prebilattice X1 X2 l1 l2).
  Proof.
    use iscontraprop1.
    - use isapropdirprod; use isaprop_islatticeop.
    - exact (make_prod_prebilattice l1 l2).
  Defined.

  Definition prod_prebilattice_to_prebilattice {X1 X2 : hSet} {l1 : lattice X1} {l2 : lattice X2} (b : prod_prebilattice X1 X2 l1 l2) : prebilattice (prod_prebilattice_carrier X1 X2) :=  make_prebilattice (make_lattice (pr1 b)) (make_lattice (pr2 b)) .

  Coercion prod_prebilattice_to_prebilattice : prod_prebilattice >-> prebilattice .
End definition .

Section bounded.
  Definition prod_prebilattice_false {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_prebilattice_carrier X1 X2) :=
    Lbot bl1,, Ltop bl2 .
  Definition prod_prebilattice_true  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_prebilattice_carrier X1 X2) :=
    Ltop bl1,, Lbot bl2 .
  Definition prod_prebilattice_bottom {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_prebilattice_carrier X1 X2):=
    Lbot bl1,, Lbot bl2 .
  Definition prod_prebilattice_top {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : (prod_prebilattice_carrier X1 X2) :=  Ltop bl1,, Ltop bl2.

  Definition bounded_prod_prebilattice (X1 X2 : hSet) (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) :=
    bounded_latticeop (make_lattice (islatticeop_prod_t bl1 bl2)) (prod_prebilattice_false bl1 bl2) (prod_prebilattice_true bl1 bl2)
                      × bounded_latticeop (make_lattice (islatticeop_prod_k bl1 bl2)) (prod_prebilattice_bottom bl1 bl2) (prod_prebilattice_top bl1 bl2).

  Definition bounded_islatticeop_prod_t  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (make_lattice (islatticeop_prod_t bl1 bl2)) (prod_prebilattice_false bl1 bl2) (prod_prebilattice_true bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop | use islunit_Lmax_Lbot].
  Defined.

  Definition bounded_islatticeop_prod_k  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_latticeop (make_lattice (islatticeop_prod_k bl1 bl2)) (prod_prebilattice_bottom bl1 bl2) (prod_prebilattice_top bl1 bl2) .
  Proof.
    use make_dirprod; intro; use dirprod_paths; [use islunit_Lmax_Lbot | use islunit_Lmax_Lbot | use islunit_Lmin_Ltop | use islunit_Lmin_Ltop].
  Defined.

  Definition make_bounded_prod_prebilattice  {X1 X2 : hSet} (bl1 : bounded_lattice X1) (bl2 : bounded_lattice X2) : bounded_prod_prebilattice X1 X2 bl1 bl2 := bounded_islatticeop_prod_t bl1 bl2,,bounded_islatticeop_prod_k bl1 bl2 .

  Lemma iscontr_bounded_prod_prebilattice {X1 X2 : hSet} (l1 : bounded_lattice X1) (l2 : bounded_lattice X2) : iscontr (bounded_prod_prebilattice X1 X2 l1 l2).
  Proof.
    use iscontraprop1.
    - do 2 (use isapropdirprod); use isapropislunit.
    - exact (make_bounded_prod_prebilattice l1 l2).
  Defined.

  Definition bounded_prod_prebilattices_to_prod_prebilattices {X1 X2 : hSet} {bl1 : bounded_lattice X1} {bl2 : bounded_lattice X2} (b : bounded_prod_prebilattice X1 X2 bl1 bl2) : prod_prebilattice X1 X2 bl1 bl2 := pr221 (make_bounded_lattice (pr1 b)),, pr221 (make_bounded_lattice (pr2 b)).

  Coercion bounded_prod_prebilattices_to_prod_prebilattices : bounded_prod_prebilattice >-> prod_prebilattice.

  Definition bounded_prod_prebilattices_to_bounded_prebilattices {X1 X2 : hSet} {l1 : bounded_lattice X1} {l2 : bounded_lattice X2} (b : bounded_prod_prebilattice X1 X2 l1 l2) : bounded_prebilattice (prod_prebilattice_carrier X1 X2) :=  make_bounded_prebilattice (make_bounded_lattice (pr1 b)) (make_bounded_lattice (pr2 b)) .

  Coercion bounded_prod_prebilattices_to_bounded_prebilattices : bounded_prod_prebilattice >-> bounded_prebilattice .
End bounded.

Section properties.
  Proposition prod_prebilattices_are_interlaced {X1 X2 : hSet} {l1 : lattice X1} {l2 : lattice X2} (b : prod_prebilattice X1 X2 l1 l2) : is_interlaced b .
  Proof.
    do 3 (try use make_dirprod); intros [x1 x2] [y1 y2] [z1 z2] H; use dirprod_paths; cbn in H; set (H1 := maponpaths dirprod_pr1 H); cbn in H1; set (H2 := maponpaths dirprod_pr2 H); cbn in H2; cbn.
    - rewrite (iscomm_Lmin _ x1 z1), isassoc_Lmin, <- (isassoc_Lmin _ x1 y1 z1), H1, (iscomm_Lmin _ x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmax_ge_eq_l; use Lmin_ge_case.
      -- use (istrans_Lge _ x2 y2 (Lmin _ y2 z2)).
         --- rewrite <- H2; exact (Lmax_ge_r _ x2 y2).
         --- exact (Lmin_ge_l _ y2 z2).
      -- exact (Lmin_ge_r _ y2 z2).
    - use Lmin_ge_eq_l; use Lmax_ge_case.
      -- use (istrans_Lle _ x1 y1 (Lmax _ y1 z1)).
         --- rewrite <- H1; exact (Lmin_ge_r _ x1 y1).
         --- exact (Lmax_ge_l _ y1 z1).
      -- exact (Lmax_ge_r _ y1 z1).
    - rewrite (iscomm_Lmax _ x2 z2), (isassoc_Lmax), <- (isassoc_Lmax _ x2 y2 z2), H2, (iscomm_Lmax _ x2 z2), <- isassoc_Lmax, Lmax_id. reflexivity.
    - rewrite (iscomm_Lmin _ x1 z1), isassoc_Lmin, <- (isassoc_Lmin _ x1 y1 z1), H1, (iscomm_Lmin _ x1 z1), <- isassoc_Lmin, Lmin_id; reflexivity .
    - use Lmin_ge_eq_l. use Lmax_le_case.
      -- use (istrans_Lle _ x2 y2 (Lmax _ y2 z2)).
         --- rewrite <- H2. exact (Lmin_le_r _ x2 y2).
         --- exact (Lmax_ge_l _ y2 z2).
      -- exact (Lmax_le_r _ y2 z2).
    - use Lmin_ge_eq_l; use Lmax_ge_case.
      -- use (istrans_Lle _ x1 y1 (Lmax _ y1 z1)).
         --- rewrite <- H1; exact (Lmin_ge_r _ x1 y1).
         --- exact (Lmax_ge_l _ y1 z1).
      -- exact (Lmax_ge_r _ y1 z1).
    - rewrite (iscomm_Lmin _ x2 z2), (isassoc_Lmin), <- (isassoc_Lmin _ x2 y2 z2), H2, (iscomm_Lmin _ x2 z2), <- isassoc_Lmin, Lmin_id. reflexivity.
  Defined.
End properties.

(**
The representation theorem states that every interlaced prebilattice
is isomorphic to a product prebilattice
(thus, inverting prod_prebilattices_are_interlaced in some sense).

The proof below follows the steps of Section 3.1 of the paper
Félix Bou and Umberto Rivieccio. The logic of distributive bilattices. Logic
Journal of IGPL, 19(1):183–216. doi:10.1093/jigpal/jzq041

The relation ~1 of the paper is here named rel_same_SW2NE,
since two elements related by this relation are in the same
southwest-to-northeast 'axis' of the prebilattice.
Similarly, ~2 of the paper is here named rel_same_SE2NW.
**)
Section representation_theorem.
  Definition rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : hrel X := λ x y : X, eqset (join b x y) (consensus b x y)  .
  Lemma isEq_rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : iseqrel (rel_same_SW2NE b).
  Proof.
    do 2 (try split).
    - intros x y z H1 H2. use (isantisymm_Lle (tlattice b)).
      -- use Lmax_le_case.
         --- assert (r1 : tle b x (consensus b (consensus b x y) z) ).
             {
               use (istrans_tle _  x (consensus b x y)).
               - rewrite <- H1. apply (Lmax_le_l (tlattice _)).
               - rewrite (isassoc_consensus _ x y z), (iscomm_consensus _ x y), <- H2, (iscomm_consensus _ x).
                 use interlacing_consensus_t. use Lmin_absorb .
             }
             set (r2 := Lmin_le_r _ _ _ : kle b (consensus b (consensus b x y) z) z ).
             rewrite iscomm_consensus. use (interlaced_leqt_leqk_leqtconsensus _ _ _ (_,,r1,,r2)).
         --- set (r1 := Lmax_le_r _ _ _  : tle b z (join b (join b x y) z) ).
             assert (r2 : kle b (join b (join b x y) z) x).
             {
               use (istrans_kle _ (join _ (join b x y) z) (join b x y)).
               - rewrite (isassoc_join _ x y z), (iscomm_join _ x y), H2, (iscomm_join _ x).
                 use interlacing_join_k. use Lmin_le_l.
               - rewrite H1. use Lmin_le_l.
             }
             use (interlaced_leqt_leqk_leqtconsensus _ _ _ (_,,r1,,r2)).
      -- use (top_interlacing_consensus_t (Lmax_le_l _ x z) (Lmax_le_r _ x z)).
    - intro. unfold rel_same_SW2NE, consensus. rewrite Lmin_id. unfold join. rewrite Lmax_id. reflexivity.
    - intros ? ? H. unfold rel_same_SW2NE. rewrite iscomm_join, iscomm_consensus. exact H.
  Defined.
  Definition eqrel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : eqrel X := make_eqrel (rel_same_SW2NE b) (isEq_rel_same_SW2NE b).

  Definition rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : hrel X := λ x y : X, eqset (meet b x y) (consensus b x y)  .
  Lemma isEq_rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : iseqrel (rel_same_SE2NW b) .
  Proof.
    exact (isEq_rel_same_SW2NE (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b))).
  Defined.
  Definition eqrel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : eqrel X := make_eqrel (rel_same_SE2NW b) (isEq_rel_same_SE2NW b).

  Lemma iscomp_consensus_rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (consensus b).
  Proof.
    intros x y w z H1 H2.
    use (isantisymm_Lle (klattice b) (join _ (consensus _ x w) (consensus _ y z)) ((consensus _ (consensus _ x w) (consensus _ y z)))).
    - rewrite (isassoc_consensus _ x w (consensus _ y z)),
        (iscomm_consensus _ y z),
        <- (isassoc_consensus _ w z y),
        (iscomm_consensus _ (consensus _ w z) y),
        <- (isassoc_consensus _ x y (consensus _ w z)).
      use Lmin_le_case.
      -- rewrite <- H1.
         use (double_interlacing_join_k (Lmin_le_l _ x w) (Lmin_le_r _ z y)).
      -- rewrite <- H2.
         use (double_interlacing_join_k (Lmin_le_r _ x w) (Lmin_le_l _ z y)).
    - use (bottom_interlacing_join_k (Lmin_le_l _ (consensus _ x w) (consensus _ y z)) (Lmin_le_r _ (consensus _ x w) (consensus _ y z))).
  Defined.

  Lemma iscomp_gullibility_rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (gullibility b).
  Proof.
    intros x y w z H1 H2.
    use (isantisymm_Lle (tlattice b) (join _ (gullibility _ x w) (gullibility _ y z)) ((consensus _ (gullibility _ x w) (gullibility _ y z)))).
    - use Lmax_le_case.
      -- rewrite iscomm_consensus.
         use (interlaced_leqt_leqk_leqtconsensus _ (gullibility _ x w) (gullibility _ y z)).
         exists (gullibility b (join b x y) (join b w z)).
         split.
         ---use (double_interlacing_gullibility_t (Lmax_le_l _ x y) (Lmax_le_l _ w z)).
         --- rewrite H1, H2.
             use Lmax_le_case.
             ---- use (istrans_Lle _ _ y _).
                  ----- use Lmin_le_r.
                  ----- use Lmax_le_l.
             ---- use (istrans_Lle _ _ z _).
                  ----- use Lmin_le_r.
                  ----- use Lmax_le_r.
      -- use (interlaced_leqt_leqk_leqtconsensus _ (gullibility _ y z) (gullibility _ x w)).
         exists (gullibility b (join b x y) (join b w z)).
         split.
         --- use (double_interlacing_gullibility_t (Lmax_le_r _ _ _) (Lmax_le_r _ _ _)).
         --- rewrite H1, H2.
             use Lmax_le_case.
             ---- use (istrans_Lle _ _ x _).
                  ----- use Lmin_le_l.
                  ----- use Lmax_le_l.
             ---- use (istrans_Lle _ _ w _).
                  ----- use Lmin_le_l.
                  ----- use Lmax_le_r.
    - use (top_interlacing_consensus_t (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
  Defined.

  Lemma iscomp_consensus_rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SE2NW b) (eqrel_same_SE2NW b) (consensus b) .
  Proof.
    exact (iscomp_consensus_rel_same_SW2NE (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b))).
  Defined.
  Lemma iscomp_gullibility_rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SE2NW b) (eqrel_same_SE2NW b) (gullibility b) .
  Proof.
    exact (iscomp_gullibility_rel_same_SW2NE (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b))).
  Defined.
  Lemma iscomp_meet_rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SE2NW b) (eqrel_same_SE2NW b) (meet b).
  Proof.
    intros ? ? ? ? H1 H2.
    use (!iscomp_consensus_rel_same_SE2NW (make_interlaced_prebilattice (dual_prebilattice_is_interlaced b)) _ _ _ _ (!H1) (!H2)).
  Defined.

  Lemma iscomp_join_rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (join b) .
  Proof.
    exact (iscomp_meet_rel_same_SE2NW (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b))).
  Defined.

  Lemma rel_same_SW2NE_meet_consensus {X : hSet} (b : interlaced_prebilattice X) (x y : X): rel_same_SW2NE b (meet b x y) (consensus b x y).
  Proof.
    use (isantisymm_Lle (tlattice b)).
    - use Lmax_le_case.
      -- rewrite (iscomm_consensus _ (meet _ _ _) _ ) .
         use interlaced_leqt_leqk_leqtconsensus.
         exists (consensus b x y).
         split.
         --- use (bottom_interlacing_consensus_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
      -- use interlaced_leqk_leqt_leqtconsensus.
         exists (meet b x y).
         split.
         --- use (bottom_interlacing_meet_k (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
    - use (top_interlacing_consensus_t (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
  Defined.

  Lemma iscomp_meet_rel_same_SW2NE {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (meet b).
  Proof.
    intros x y z w ? ?.
    use (eqreltrans (eqrel_same_SW2NE b) _ (consensus b x z) _ (rel_same_SW2NE_meet_consensus _ _ _)).
    use (eqreltrans (eqrel_same_SW2NE b) _ (consensus b y w) _ (iscomp_consensus_rel_same_SW2NE _ _ _ _ _ _ _)).
    - assumption.
    - assumption.
    - use eqrelsymm. use rel_same_SW2NE_meet_consensus.
  Defined.

  Lemma iscomp_join_rel_same_SE2NW {X : hSet} (b : interlaced_prebilattice X) : iscomprelrelfun2 (eqrel_same_SE2NW b) (eqrel_same_SE2NW b) (join b) .
  Proof.
    exact (iscomp_meet_rel_same_SW2NE (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b))).
  Defined.

  Lemma rel_same_SE2NW_join_consensus {X : hSet} (b : interlaced_prebilattice X) (x y : X) : rel_same_SE2NW b (join b x y) (consensus b x y)
  .
  Proof.
    exact (rel_same_SW2NE_meet_consensus (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b)) x y).
  Defined.
  Lemma rel_same_SE2NW_meet_gullibility {X : hSet} (b : interlaced_prebilattice X) (x y : X) : rel_same_SE2NW b (meet b x y) (gullibility b x y).
  Proof.
    use (isantisymm_Lle (tlattice b)).
    - use (bottom_interlacing_consensus_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
    - use Lmin_le_case.
      -- rewrite iscomm_consensus.
         use interlaced_leqk_geqt_geqtconsensus.
         exists (gullibility b x y).
         split.
         --- exact (top_interlacing_meet_k (Lmax_le_l _ _ _) (Lmax_le_r _ _ _)).
         --- use isrefl_Lle.
      -- use interlaced_geqt_leqk_geqtconsensus .
         exists (meet b x y).
         split.
         --- exact (bottom_interlacing_gullibility_t (Lmin_le_l _ _ _) (Lmin_le_r _ _ _)).
         --- use isrefl_Lle.
  Defined.

  Lemma rel_same_SW2NE_join_gullibility {X : hSet} (b : interlaced_prebilattice X) (x y : X) : rel_same_SW2NE b (join b x y) (gullibility b x y) .
  Proof.
    exact (rel_same_SE2NW_meet_gullibility (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b)) x y).
  Defined.

  Definition lattice_SW2NE {X : hSet} (b : interlaced_prebilattice X) : lattice (setquotinset (rel_same_SW2NE b)).
  Proof.
    set (iscc := iscomp_consensus_rel_same_SW2NE b).
    set (iscg := iscomp_gullibility_rel_same_SW2NE b).
    set (cc := setquotfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (consensus b) iscc).
    set (gg := setquotfun2 (eqrel_same_SW2NE b) (eqrel_same_SW2NE b) (gullibility b) iscg).
    exists cc, gg.
    do 4 (try split).
    - use (isassocsetquotfun2 (consensus b) iscc (isassoc_Lmin (klattice b))).
    - use (iscommsetquotfun2 (consensus b) iscc (iscomm_consensus b)).
    - use (isassocsetquotfun2 (gullibility b) iscg (isassoc_Lmax (klattice b))).
    - use (iscommsetquotfun2 (gullibility b) iscg (iscomm_gullibility b)).
    - use (setquotuniv2prop _ (λ x y, @eqset (setquotinset _) (cc x (gg x y)) x)).
      intros x y.
      cbn.
      rewrite (consensus_gullibility_absorb b).
      reflexivity.
    - use (setquotuniv2prop _ (λ x y, @eqset (setquotinset _) (gg x (cc x y)) x)).
      intros x y.
      cbn.
      rewrite (gullibility_consensus_absorb b).
      reflexivity.
  Defined.

  Definition lattice_SE2NW {X : hSet} (b : interlaced_prebilattice X) : lattice (setquotinset (rel_same_SE2NW b)) :=
    lattice_SW2NE (make_interlaced_prebilattice (t_opp_prebilattice_is_interlaced b)).

  Lemma SE2NW_and_SW2NE_is_id {X : hSet} (b : interlaced_prebilattice X) (x y : X) (p1 : rel_same_SW2NE b x y) (p2 : rel_same_SE2NW b x y) : x = y.
  Proof.
    set (p := p1 @ !p2).
    use (isantisymm_Lle (tlattice b)).
    - use (istrans_Lle (tlattice _) x (join b x y) y (Lmax_le_l _ _ _)).
      rewrite p.
      use Lmin_le_r.
    - use (istrans_Lle (tlattice _) y (join b x y) x (Lmax_le_r _ _ _)).
      rewrite p.
      use Lmin_le_l.
  Defined.

  Definition interlaced_prebilattice_to_prod {X : hSet} (b : interlaced_prebilattice X) : ∑ (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) , prod_prebilattice X1 X2 l1 l2 :=
    setquotinset (rel_same_SW2NE b),, setquotinset (rel_same_SE2NW b),,lattice_SW2NE b,,lattice_SE2NW b,,make_prod_prebilattice (lattice_SW2NE b) (lattice_SE2NW b).

  Lemma interlaced_carrier_to_prod_carrier {X : hSet} (b : interlaced_prebilattice X) : weq X (prod_prebilattice_carrier (setquotinset (rel_same_SW2NE b)) (setquotinset (rel_same_SE2NW b))) .
  Proof.
    (** First, move calculation from equivalence classes to representatives **)
    exists (λ x, setquotpr (eqrel_same_SW2NE b) x,, setquotpr (eqrel_same_SE2NW b) x).
    intro y; destruct y as [yL yR].
    set (TL := λ yL, λ yR : setquotinset (rel_same_SE2NW b), hfiber (λ x : X, setquotpr (eqrel_same_SW2NE b) x,, setquotpr (eqrel_same_SE2NW b) x) (yL,, yR)).
    use (setquotunivprop (eqrel_same_SW2NE b) (λ yL, make_hProp (iscontr (TL yL yR)) (isapropiscontr (TL yL yR)))).
    intro y1.
    set (TR := λ yR, TL (setquotpr (eqrel_same_SW2NE b) y1) yR).
    use (setquotunivprop (eqrel_same_SE2NW b) (λ yR, make_hProp (iscontr (TR yR)) (isapropiscontr (TR yR)))).
    intro y2.

    (** Then, define the center of contraction  **)
    set (c := consensus b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))).
    assert (HL : setquotpr (eqrel_same_SW2NE b) c = setquotpr (eqrel_same_SW2NE b) y1).
    {
      use weqpathsinsetquot.
      use (eqreltrans _ _ (meet b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))) _ ).
      {
        use eqrelsymm.
        use rel_same_SW2NE_meet_consensus.
      }
      use (eqreltrans _ _ (meet b (meet b y1 (join b y1 y2)) (join b y2 (join b y1 y2))) _ ).
      {
        use iscomp_meet_rel_same_SW2NE.
        - use iscomp_meet_rel_same_SW2NE.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rel_same_SW2NE_join_gullibility.
        - use iscomp_join_rel_same_SW2NE.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rel_same_SW2NE_join_gullibility.
      }
      rewrite meet_join_absorb,
        iscomm_join,
        isassoc_join,
        join_id,
        meet_join_absorb.
      use eqrelrefl.
    }
    assert (HR : setquotpr (eqrel_same_SE2NW b) c = setquotpr (eqrel_same_SE2NW b) y2).
    {
      use weqpathsinsetquot.
      use (eqreltrans _ _ (join b (meet b y1 (gullibility b y1 y2)) (join b y2 (gullibility b y1 y2))) _ ).
      {
        use eqrelsymm.
        use rel_same_SE2NW_join_consensus.
      }
      use (eqreltrans _ _ (join b (meet b y1 (meet b y1 y2)) (join b y2 (meet b y1 y2))) _ ).
      {
        use iscomp_join_rel_same_SE2NW.
        - use iscomp_meet_rel_same_SE2NW.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rel_same_SE2NW_meet_gullibility.
        - use iscomp_join_rel_same_SE2NW.
          -- use eqrelrefl.
          -- use eqrelsymm.
             use rel_same_SE2NW_meet_gullibility.
      }
      rewrite (iscomm_meet _ y1 (meet _ _ _)),
        (iscomm_meet _ y1 y2),
        isassoc_meet,
        meet_id,
        join_meet_absorb,
        iscomm_join,
        join_meet_absorb.
      use eqrelrefl.
    }
    exists (c,,pathsdirprod HL HR).

    (** and prove that it is a center of contraction **)
    intro t.
    use total2_paths_f.
    - use (! SE2NW_and_SW2NE_is_id _ _ _
             (invmap (weqpathsinsetquot _ _ _) (HL @ ! (maponpaths pr1 (pr2 t))))
             (invmap (weqpathsinsetquot _ _ _) (HR @ ! (maponpaths dirprod_pr2 (pr2 t))))
          ).
    - use (proofirrelevance_hProp (
               @eqset
                 (make_hSet _ (isaset_dirprod (isasetsetquot (eqrel_same_SW2NE b)) (isasetsetquot (eqrel_same_SE2NW b))))
                 (setquotpr (eqrel_same_SW2NE b) c,, setquotpr (eqrel_same_SE2NW b) c)
                 (setquotpr (eqrel_same_SW2NE b) y1,, setquotpr (eqrel_same_SE2NW b) y2)
          )).
  Defined.

  Definition iso_interlaced_product {X : hSet} (b : interlaced_prebilattice X) : @Isos.iso (precategory_data_from_precategory prebilattice_disp_category) (X,, (pr1 b))
                                                                                           (prod_prebilattice_carrier (pr1 (interlaced_prebilattice_to_prod b))
                                                                                                                      (pr12 (interlaced_prebilattice_to_prod b)),,
                                                                                                                      (pr1 (make_interlaced_prebilattice
                                                                                                                              (prod_prebilattices_are_interlaced (pr222 (pr2 (interlaced_prebilattice_to_prod b))))))).
  Proof.
    use (prebilattice_iso b (make_interlaced_prebilattice (prod_prebilattices_are_interlaced (pr2 (pr222 (interlaced_prebilattice_to_prod b))))) (interlaced_carrier_to_prod_carrier b)).
    intros x y.
    do 4 (try use make_dirprod); use dirprod_paths;
    use pathsinv0;
    try (use (iscompsetquotpr (eqrel_same_SW2NE _)));
    try (use (iscompsetquotpr (eqrel_same_SE2NW _))).
    - use (rel_same_SW2NE_meet_consensus).
    - use (rel_same_SE2NW_meet_gullibility).
    - use (rel_same_SW2NE_join_gullibility).
    - use (rel_same_SE2NW_join_consensus).
    - use (pr21 (isEq_rel_same_SW2NE _)).
    - use (pr21 (isEq_rel_same_SE2NW _)).
    - use (pr21 (isEq_rel_same_SW2NE _)).
    - use (pr21 (isEq_rel_same_SE2NW _)).
  Defined.

  Definition interlaced_prebilattice_eq_product {X : hSet} (b : interlaced_prebilattice X) : ∑ (X1 X2 : hSet) (l1 : lattice X1) (l2 : lattice X2) (b' : prod_prebilattice X1 X2 l1 l2), (X,, (interlaced_prebilattice_to_prebilattice b)) = (prod_prebilattice_carrier X1 X2,, (prod_prebilattice_to_prebilattice b')).
  Proof.
    set (interlacedToProd := interlaced_prebilattice_to_prod b).
    exists (pr1 interlacedToProd).
    exists (pr12 interlacedToProd).
    exists (pr122 interlacedToProd).
    exists (pr1 (pr222 interlacedToProd)).
    exists (pr2 (pr222 interlacedToProd)).
    exact (isotoid prebilattice_disp_category is_univalent_prebilattice_disp_category (Isos.iso_to_z_iso (iso_interlaced_product b))).
  Defined.
End representation_theorem.
