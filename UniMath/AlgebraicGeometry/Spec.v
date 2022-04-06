(** ** Contents

- Zariski topology
- Structure sheaf
  - Sections
  - Restriction of a section
  - Definition of the structure sheaf
 *)

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.RigsAndRings.Ideals.
Require Import UniMath.MoreFoundations.AxiomOfChoice.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.commrings.
Require Import UniMath.AlgebraicGeometry.Topology.
Require Import UniMath.AlgebraicGeometry.SheavesOfRings.

Local Open Scope cat.
Local Open Scope ring.
Local Open Scope logic.
Local Open Scope subtype.
Local Open Scope open.

(** ** Zariski topology *)

Section spec.
  Context {R : commring}.

  Definition zariski_topology : (prime_ideal R -> hProp) -> hProp :=
    λ U, ∃ A, U ≡ (λ p, A ⊈ p).

  Lemma zariski_topology_union :
    isSetOfOpen_union zariski_topology.
  Proof.
    intros O H0. unfold zariski_topology.
    set (S := λ A, ∃ U, O U ∧ U ≡ (λ p, A ⊈ p)).
    apply hinhpr. exists (union S). intro p.
    apply issymm_logeq, (logeq_trans (union_not_contained_in S p)).
    unfold union. use make_dirprod; intro H.
    - use (hinhuniv _ H); intro HA.
      induction HA as [A HA].
      use (hinhfun _ (dirprod_pr1 HA)); intro HU.
      induction HU as [U HU].
      exists U. use make_dirprod.
      + exact (dirprod_pr1 HU).
      + apply (dirprod_pr2 (dirprod_pr2 HU p)), (dirprod_pr2 HA).
    - use (hinhuniv _ H); intro HU. induction HU as [U HU].
      use (hinhfun _ (H0 U (dirprod_pr1 HU))); intro HA.
      induction HA as [A HA].
      exists A. use make_dirprod.
      + apply hinhpr. exists U. exact (make_dirprod (dirprod_pr1 HU) HA).
      + apply (dirprod_pr1 (HA p)), (dirprod_pr2 HU).
  Defined.

  Lemma zariski_topology_htrue :
    isSetOfOpen_htrue zariski_topology.
  Proof.
    apply hinhpr. exists (λ x, htrue). intro p.
    use make_dirprod; intro H.
    - apply hinhpr. exists rigunel2.
      exact (make_dirprod tt (prime_ideal_ax2 p)).
    - exact tt.
  Defined.

  Lemma zariski_topology_and :
    isSetOfOpen_and zariski_topology.
  Proof.
    unfold zariski_topology. intros U V HU HV.
    use (hinhuniv _ HU); intros HA.
    use (hinhfun _ HV); intros HB.
    induction HA as [A HA]. induction HB as [B HB].
    exists (λ x, ∃ a b, A a × B b × x = (a * b)%ring). intro p.
    assert (H0 : U p ∧ V p ⇔ A ⊈ p ∧ B ⊈ p).
    { use make_dirprod; intro H.
      - use make_dirprod.
        + apply (dirprod_pr1 (HA p)), (dirprod_pr1 H).
        + apply (dirprod_pr1 (HB p)), (dirprod_pr2 H).
      - use make_dirprod.
        + apply (dirprod_pr2 (HA p)), (dirprod_pr1 H).
        + apply (dirprod_pr2 (HB p)), (dirprod_pr2 H). }
    apply (logeq_trans H0). unfold subtype_notContainedIn.
    use make_dirprod; intro H.
    - use (hinhuniv _ (dirprod_pr1 H)); intro Ha.
      use (hinhfun _ (dirprod_pr2 H)); intro Hb.
      induction Ha as [a Ha]. induction Hb as [b Hb].
      exists (a * b)%ring. use make_dirprod.
      + apply hinhpr. exists a, b.
        exact (make_dirprod (dirprod_pr1 Ha)
                            (make_dirprod (dirprod_pr1 Hb) (idpath _))).
      + apply (@negf _ (p a ∨ p b)).
        * exact (prime_ideal_ax1 _ a b).
        * apply toneghdisj.
          exact (make_dirprod (dirprod_pr2 Ha) (dirprod_pr2 Hb)).
    - use (hinhuniv _ H); intro Hx.
      induction Hx as [x Hx]. induction Hx as [Hx Hpx].
      use (hinhuniv _ Hx); intro Hab.
      induction Hab as [a Hab]. induction Hab as [b Hab].
      induction Hab as [Ha Hab]. induction Hab as [Hb Hab].
      use make_dirprod; apply hinhpr.
      + exists a. use make_dirprod.
        * exact Ha.
        * use (negf _ Hpx). intro Hpa.
          apply (transportb (λ y, p y) Hab).
          apply (ideal_isr p b a), Hpa.
      + exists b. use make_dirprod.
        * exact Hb.
        * use (negf _ Hpx). intro Hpb.
          apply (transportb (λ y, p y) Hab).
          apply (ideal_isl p a b), Hpb.
  Defined.

  Definition Spec : TopologicalSpace :=
    mkTopologicalSpace (make_hSet (prime_ideal R) isaset_prime_ideal)
                       zariski_topology
                       zariski_topology_union
                       zariski_topology_htrue
                       zariski_topology_and.
End spec.

Arguments Spec _ : clear implicits.


(** ** Structure sheaf *)

(** *** Sections *)

(** For each prime ideal p of R, let R_p be the localization of R at p. For an open set U from the
    spectrum of R, we define [section U] to be the family of functions s : ∏ p, R_p, such that s is
    locally a quotient of elements of R: to be precise, we require that for each p in U there is a
    neighborhood V of p, contained in U, and elements f, g in R, such that for each q in V, g not in
    q, and s q = f/g. *)

Section section.
  Context {R : commring} {U : @Open (Spec R)}.

  Definition is_quotient_on (V : Open)
                            (s : ∏ q : carrier U, localization_at (pr1 q)) : hProp :=
    ∃ (f g : R), ∀ q : carrier U,
        V (pr1 q) ⇒ ∃ Hg : ¬ (pr1 q : prime_ideal R) g, s q = quotient f (g ,, Hg).

  Definition is_section (s : ∏ p : carrier U, localization_at (pr1 p)) : hProp :=
    ∀ p : carrier U, ∃ V : Open, V (pr1 p) ∧ V ⊆ U ∧ is_quotient_on V s.

  Definition section : UU :=
    ∑ s : (∏ p : carrier U, localization_at (pr1 p)), is_section s.

  Definition make_section (s : ∏ p : carrier U, localization_at (pr1 p)) (H : is_section s) :
    section := s ,, H.

  Definition section_map (s : section) : ∏ p : carrier U, localization_at (pr1 p) := pr1 s.
  Coercion section_map : section >-> Funclass.

  Definition section_prop (s : section) : is_section s := pr2 s.

  Definition funext_section (s t : section) : (∀ p, s p = t p) -> s = t :=
    λ H, subtypePath_prop (funextsec _ _ _ H).
End section.

Arguments section {_} _.


(* [section U] is a commutative ring. *)

Section section_commring.
  Context {R : commring} {U : @Open (Spec R)}.

  Lemma isaset_section : isaset (section U).
  Proof.
    apply isaset_total2.
    - apply impred_isaset. intro p. apply setproperty.
    - intro s. apply isasetaprop, propproperty.
  Qed.

  Definition section_hset : hSet :=
    make_hSet _ isaset_section.

  Lemma is_section_op1 (s t : section U) : is_section (λ p, s p + t p).
  Proof.
    intro p.
    induction s as [s Hs].
    induction t as [t Ht].
    use (hinhuniv _ (Hs p)); intro H1.
    use (hinhuniv _ (Ht p)); intro H2.
    induction H1 as [V1 H1]. induction H1 as [Hp1 H1]. induction H1 as [HU1 H1].
    induction H2 as [V2 H2]. induction H2 as [Hp2 H2]. induction H2 as [HU2 H2].
    use (hinhuniv _ H1); intro Hfg1.
    use (hinhuniv _ H2); intro Hfg2.
    induction Hfg1 as [f1 Hfg1]. induction Hfg1 as [g1 Hq1].
    induction Hfg2 as [f2 Hfg2]. induction Hfg2 as [g2 Hq2].
    apply hinhpr. exists (V1 ∩ V2). use make_dirprod.
    - exact (make_dirprod Hp1 Hp2).
    - use make_dirprod.
      + intros x Hx. apply (HU1 x), (dirprod_pr1 Hx).
      + apply hinhpr. exists (g2 * f1 + g1 * f2), (g1 * g2). intros q HVq.
        use (hinhuniv _ (Hq1 q (dirprod_pr1 HVq))); intro Hg1.
        use (hinhuniv _ (Hq2 q (dirprod_pr2 HVq))); intro Hg2.
        induction Hg1 as [Hg1 Heq1].
        induction Hg2 as [Hg2 Heq2].
        set (Hg := prime_ideal_ax1_contraposition (pr1 q) _ _ Hg1 Hg2).
        apply hinhpr. exists Hg. exact (map_on_two_paths op1 Heq1 Heq2 @ idpath _).
  Qed.

  Definition section_op1 : binop (section U) :=
    λ s t, make_section _ (is_section_op1 s t).

  Lemma isassoc_section_op1 : isassoc section_op1.
  Proof.
    intros r s t. apply funext_section.
    intro p. simpl. apply (rigassoc1 (localization_at (pr1 p))).
  Qed.

  Lemma iscomm_section_op1 : iscomm section_op1.
  Proof.
    intros s t. apply funext_section.
    intro p. simpl. apply (rigcomm1 (localization_at (pr1 p))).
  Qed.

  Lemma is_section_unel1 : is_section (λ p : carrier U, @rigunel1 (localization_at (pr1 p))).
  Proof.
    intro p. apply hinhpr.
    exists U. use make_dirprod.
    - exact (pr2 p).
    - use make_dirprod.
      + intros x H. exact H.
      + apply hinhpr. exists 0, 1. intros q Hq.
        apply hinhpr. exists (prime_ideal_ax2 _). apply idpath.
  Qed.

  Definition section_unel1 : section U :=
    make_section _ is_section_unel1.

  Lemma islunit_section_unel1 : islunit section_op1 section_unel1.
  Proof.
    intro s. apply funext_section.
    intro p. apply (riglunax1 (localization_at (pr1 p))).
  Qed.

  Lemma isrunit_section_unel1 : isrunit section_op1 section_unel1.
  Proof.
    apply (@weqlunitrunit section_hset).
    - exact iscomm_section_op1.
    - exact islunit_section_unel1.
  Qed.

  Lemma isunit_section_unel1 : isunit section_op1 section_unel1.
  Proof.
    exact (make_dirprod islunit_section_unel1 isrunit_section_unel1).
  Qed.

  Definition ismonoidop_section_op1 : ismonoidop section_op1 :=
    make_ismonoidop isassoc_section_op1
                    (make_isunital section_unel1 isunit_section_unel1).

  Lemma is_section_inv (s : section U) : is_section (λ p, - s p).
  Proof.
    intro p.
    induction s as [s Hs].
    use (hinhuniv _ (Hs p)); intro H.
    induction H as [V H]. induction H as [HVp H]. induction H as [HV H].
    use (hinhuniv _ H); intro Hfg.
    induction Hfg as [f Hfg]. induction Hfg as [g Hfg].
    apply hinhpr. exists V. use make_dirprod.
    - exact HVp.
    - use make_dirprod.
      + exact HV.
      + apply hinhpr. exists (-1 * f), g.
        intros q Hq.
        use (hinhuniv _ (Hfg q Hq)); intros Hg.
        induction Hg as [Hg Heq].
        apply hinhpr. exists Hg. exact (maponpaths ringinv1 Heq @ idpath _).
  Qed.

  Definition section_inv : section U -> section U :=
    λ s, make_section _ (is_section_inv s).

  Lemma islinv_section_inv : islinv section_op1 section_unel1 section_inv.
  Proof.
    intro s. apply funext_section.
    intro p. simpl. apply (ringlinvax1 (localization_at (pr1 p))).
  Qed.

  Lemma isrinv_section_inv : isrinv section_op1 section_unel1 section_inv.
  Proof.
    apply (@weqlinvrinv section_hset).
    - exact iscomm_section_op1.
    - exact islinv_section_inv.
  Qed.

  Lemma isinv_section_inv : isinv section_op1 section_unel1 section_inv.
  Proof.
    exact (make_isinv islinv_section_inv isrinv_section_inv).
  Qed.

  Definition invstruct_section_op1 : invstruct section_op1 ismonoidop_section_op1.
  Proof.
    use make_invstruct.
    - exact section_inv.
    - exact isinv_section_inv.
  Defined.

  Definition isgrop_section_op1 : isgrop section_op1 :=
    make_isgrop ismonoidop_section_op1 invstruct_section_op1.

  Lemma is_section_op2 (s t : section U) : is_section (λ p, s p * t p).
  Proof.
    intros p.
    induction s as [s Hs].
    induction t as [t Ht].
    use (hinhuniv _ (Hs p)); intro H1.
    use (hinhuniv _ (Ht p)); intro H2.
    induction H1 as [V1 H1]. induction H1 as [Hp1 H1]. induction H1 as [HU1 H1].
    induction H2 as [V2 H2]. induction H2 as [Hp2 H2]. induction H2 as [HU2 H2].
    use (hinhuniv _ H1); intro Hfg1.
    use (hinhuniv _ H2); intro Hfg2.
    induction Hfg1 as [f1 Hfg1]. induction Hfg1 as [g1 Hq1].
    induction Hfg2 as [f2 Hfg2]. induction Hfg2 as [g2 Hq2].
    apply hinhpr. exists (V1 ∩ V2). use make_dirprod.
    + exact (make_dirprod Hp1 Hp2).
    + use make_dirprod.
      * intros x Hx. apply (HU1 x), (dirprod_pr1 Hx).
      * apply hinhpr. exists (f1 * f2), (g1 * g2). intros q HVq.
        use (hinhuniv _ (Hq1 q (dirprod_pr1 HVq))); intro Hg1.
        use (hinhuniv _ (Hq2 q (dirprod_pr2 HVq))); intro Hg2.
        induction Hg1 as [Hg1 Heq1].
        induction Hg2 as [Hg2 Heq2].
        set (Hg := prime_ideal_ax1_contraposition (pr1 q) _ _ Hg1 Hg2).
        apply hinhpr. exists Hg. exact (map_on_two_paths op2 Heq1 Heq2 @ idpath _).
  Qed.

  Definition section_op2 : binop (section U) :=
    λ s t, make_section _ (is_section_op2 s t).

  Lemma isassoc_section_op2 : isassoc section_op2.
  Proof.
    intros r s t. apply funext_section.
    intro p. simpl. apply (rigassoc2 (localization_at (pr1 p))).
  Qed.

  Lemma iscomm_section_op2 : iscomm section_op2.
  Proof.
    intros s t. apply funext_section.
    intro p. simpl. apply (rigcomm2 (localization_at (pr1 p))).
  Qed.

  Lemma is_section_unel2 :
    is_section (λ p : carrier U, @rigunel2 (localization_at (pr1 p))).
  Proof.
    intro p. apply hinhpr.
    exists U. use make_dirprod.
    - exact (pr2 p).
    - use make_dirprod.
      + intros x H. exact H.
      + apply hinhpr. exists 1, 1. intros q Hq.
        apply hinhpr. exists (prime_ideal_ax2 _). apply idpath.
  Qed.

  Definition section_unel2 : section U :=
    make_section _ is_section_unel2.

  Lemma islunit_section_unel2 : islunit section_op2 section_unel2.
  Proof.
    intro s. apply funext_section.
    intro p. apply (riglunax2 (localization_at (pr1 p))).
  Qed.

  Lemma isrunit_section_unel2 : isrunit section_op2 section_unel2.
  Proof.
    apply (@weqlunitrunit section_hset).
    - exact iscomm_section_op2.
    - exact islunit_section_unel2.
  Qed.

  Lemma isunit_section_unel2 : isunit section_op2 section_unel2.
  Proof.
    exact (make_dirprod islunit_section_unel2 isrunit_section_unel2).
  Qed.

  Definition ismonoidop_section_op2 : ismonoidop section_op2 :=
    make_ismonoidop isassoc_section_op2
                    (make_isunital section_unel2 isunit_section_unel2).

  Lemma isldistr_section_ops : isldistr section_op1 section_op2.
  Proof.
    intros r s t. apply funext_section.
    intro p. simpl. apply (rigldistr (localization_at (pr1 p))).
  Qed.

  Lemma isrdistr_section_ops : isrdistr section_op1 section_op2.
  Proof.
    apply (@weqldistrrdistr section_hset).
    - exact iscomm_section_op2.
    - exact isldistr_section_ops.
  Qed.

  Lemma isdistr_section_ops : isdistr section_op1 section_op2.
  Proof.
    exact (isldistr_section_ops ,, isrdistr_section_ops).
  Qed.

  Definition section_commring : commring :=
    @commringconstr section_hset section_op1 section_op2
                    isgrop_section_op1 iscomm_section_op1
                    ismonoidop_section_op2 iscomm_section_op2
                    isdistr_section_ops.
End section_commring.

Arguments section_hset {_} _.
Arguments section_commring {_} _.


(** *** Restriction of a section *)

Section restriction.
  Context {R : commring} {U V : @Open (Spec R)} (H : V ⊆ U).

  Definition restriction_section_map : (∏ p : carrier U, localization_at (pr1 p)) ->
                                       (∏ p : carrier V, localization_at (pr1 p)) :=
    λ s p, s (pr1 p ,, H (pr1 p) (pr2 p)).

  Lemma is_section_restriction_section_map (s : section U) :
    is_section (restriction_section_map s).
  Proof.
    intro p.
    induction p as [p HVp]. induction s as [s Hs].
    use (hinhuniv _ (Hs (p ,, (H _ HVp)))); intro HW.
    induction HW as [W HW]. induction HW as [HWp HW]. induction HW as [HUW Hfg].
    use (hinhfun _ Hfg); intro Hq.
    induction Hq as [f Hq]. induction Hq as [g Hq].
    exists (V ∩ W). use make_dirprod.
    - exact (make_dirprod HVp HWp).
    - use make_dirprod.
      + intros x Hx. exact (dirprod_pr1 Hx).
      + apply hinhpr. exists f, g. intros q H0. induction q as [q HVq].
        use (hinhfun _ (Hq (q ,, H _ HVq) (dirprod_pr2 H0))); intro Hg.
        induction Hg as [Hg Heq].
        exists Hg. exact Heq.
  Qed.

  Definition restriction_section : section U -> section V :=
    λ s, make_section _ (is_section_restriction_section_map s).

  (* The [restriction_section] map is a ring homomorphism. *)

  Lemma isaddmonoidfun_restriction_section :
    @ismonoidfun (rigaddabmonoid (section_commring U))
                 (rigaddabmonoid (section_commring V))
                 restriction_section.
  Proof.
    use make_ismonoidfun.
    - intros s t. apply subtypePath_prop, idpath.
    - apply subtypePath_prop, idpath.
  Qed.

  Lemma ismultmonoidfun_restriction_section :
    @ismonoidfun (rigmultmonoid (section_commring U))
                 (rigmultmonoid (section_commring V))
                 restriction_section.
  Proof.
    use make_ismonoidfun.
    - intros s t. apply subtypePath_prop, idpath.
    - apply subtypePath_prop, idpath.
  Qed.

  Lemma isringfun_restriction_section :
    @isringfun (section_commring U) (section_commring V) restriction_section.
  Proof.
    use make_isrigfun.
    - exact isaddmonoidfun_restriction_section.
    - exact ismultmonoidfun_restriction_section.
  Qed.

  Definition restriction_ringfun : ringfun (section_commring U) (section_commring V) :=
    rigfunconstr isringfun_restriction_section.
End restriction.


Section restriction_facts.
  Context {R : commring} {U V : @Open (Spec R)}.

  Lemma restriction_paths (H : V ⊆ U) (s : section U) {p : Spec R} (HUp : U p) (HVp : V p) :
    restriction_section H s (p ,, HVp) = s (p ,, HUp).
  Proof.
    induction (proofirrelevance_hProp _ (H _ HVp) HUp). apply idpath.
  Qed.

  Lemma section_subset {H : V ⊆ U} {s t : section U} :
    restriction_section H s = restriction_section H t ->
    ∏ p : carrier U, V (pr1 p) -> s p = t p.
  Proof.
    intros Heq p HVp.
    apply (@pathscomp0 _ _ (restriction_section H s (pr1 p ,, HVp))).
    - apply pathsinv0, restriction_paths.
    - apply (@pathscomp0 _ _ (restriction_section H t (pr1 p ,, HVp))).
      + induction Heq. apply idpath.
      + apply restriction_paths.
  Qed.

  Lemma section_intersection (s : section U) (t : section V) :
    restriction_section (intersection_contained1 U V) s =
    restriction_section (intersection_contained2 U V) t ->
    ∏ p (HUp : U p) (HVp : V p), s (p ,, HUp) = t (p ,, HVp).
  Proof.
    intros Heq p HUp HVp.
    set (Hp := make_dirprod HUp HVp).
    assert (H : restriction_section (intersection_contained1 U V) s (p ,, Hp) =
                restriction_section (intersection_contained2 U V) t (p ,, Hp)).
    { induction Heq. apply idpath. }
    apply H.
  Qed.
End restriction_facts.


(** *** Definition of the structure sheaf *)

Section structure_sheaf.
  Context (R : commring).

  (* presheaf *)

  Definition structure_presheaf_data :
    functor_data (open_category (Spec R))^op commring_precategory.
  Proof.
    use make_functor_data.
    - exact section_commring.
    - exact (@restriction_ringfun R).
  Defined.

  Lemma is_functor_structure_presheaf_data : is_functor structure_presheaf_data.
  Proof.
    use make_dirprod.
    - intro U.
      apply rigfun_paths, funextsec. intro s. apply subtypePath_prop, idpath.
    - intros U V W f g.
      apply rigfun_paths, funextsec. intro s. apply subtypePath_prop, idpath.
  Qed.

  Definition structure_presheaf : (open_category (Spec R))^op ⟶ commring_precategory :=
    make_functor structure_presheaf_data is_functor_structure_presheaf_data.

  (* locality *)

  Lemma locality_structure_presheaf : locality structure_presheaf.
  Proof.
    intros A s t H. apply funext_section. intro p.
    use (hinhuniv _ (hexists_open_neighborhood p)); intro HU.
    induction HU as [U HUp].
    apply (section_subset (H U)), HUp.
  Qed.

  (* gluing *)

  Definition agree_on_intersections_section {A : hsubtype (@Open (Spec R))}
                                            (g : ∏ U : A, section_commring (pr1 U)) : UU :=
    ∏ U V : A, restriction_section (intersection_contained1 _ _) (g U) =
               restriction_section (intersection_contained2 _ _) (g V).

  Definition glue_sections {A : hsubtype (@Open (Spec R))}
                           (g : ∏ U : A, section_commring (pr1 U))
                           (Hg : agree_on_intersections_section g)
                           (H : ∏ p : carrier (⋃ A), ∑ U : A, pr1 U (pr1 p)) :
    section_commring (⋃ A).
  Proof.
    use make_section; intro x; induction (H x) as [U HUx];
      set (s := g U);
      set (p := make_carrier _ _ HUx).
    - exact (section_map s p).
    - use (hinhfun _ (section_prop s p)); intro H1.
      induction H1 as [V HV]. induction HV as [HVp HV]. induction HV as [HVU HV].
      exists V. apply make_dirprod.
      + exact HVp.
      + apply make_dirprod.
        * apply (subtype_containment_istrans _ _ _ _ HVU), contained_in_union_open.
        * use (hinhfun _ HV). intro H2.
          induction H2 as [f Hh]. induction Hh as [h H3].
          exists f, h. intros q HVq. induction q as [q Hq].
          use (hinhfun _ (H3 (q ,, HVU q HVq) HVq)); intro H4.
          induction H4 as [Hh Heq].
          exists Hh. use (pathscomp0 _ Heq). simpl.
          apply section_intersection. apply Hg.
  Defined.

  Lemma gluing_structure_presheaf (ac : AxiomOfChoice) : gluing structure_presheaf.
  Proof.
    intros A g Hg.
    set (H0 := ac (carrier_subset (⋃ A)) _ (@hexists_open_neighborhood _ A)).
    use (hinhfun _ H0); intro H.
    exists (glue_sections g Hg H).
    intro U. apply funext_section.
    intro q. induction q as [q HUq]. cbn.
    apply section_intersection, Hg.
  Qed.

  (* structure sheaf *)

  Definition structure_sheaf (ac : AxiomOfChoice) : sheaf_commring (Spec R) :=
    make_sheaf_commring structure_presheaf
                        locality_structure_presheaf
                        (gluing_structure_presheaf ac).
End structure_sheaf.
