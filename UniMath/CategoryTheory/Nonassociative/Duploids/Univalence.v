(********************************************************************************

 Univalence of Duploids

 Author: B. Szilvasy
 January 2026

 We define what it means for a duploid to be univalent both as a
 single-sorted duploid ([is_dupl_univalent]), and as a split duploid
 ([is_split_dupl_univalent]). We show that the former makes shifts a
 property.

 Contents:
 1. Definition of univalence for duploids
 1.1. Single-sorted duploid univalence
 1.2. Split duploid univalence
 1.3. Algebra
 2. Consequences of univalence
 2.1. Polarity shifts are a property in single-sorted duploids
 2.2. Polarity shifts are a property in split preduploids
 3. Characterizations of univalence
 4. Split duploids and univalence

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryRXGraph.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.
Require Import UniMath.IdentitySystems.RXGraphOfRXGraphs.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.PolarizedSubcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** Definition of univalence for duploids *)
Section univalence_def.
  (** *** Single-sorted duploid univalence *)

  Definition is_dupl_univalent (M : unital_magmoid)
    := is_submm_univalent M _lt.

  Definition duploid_to_rxgraph (D : preduploid) : rxgraph
    := submm_rxgraph D _lt.

  Remark duploid_rxgraph_univalent_eq (D : preduploid)
    : is_dupl_univalent D = is_univalent (duploid_to_rxgraph D).
  Proof. reflexivity. Defined.

  Lemma is_um_univalent_preduploid_iff (D : preduploid)
    : is_dupl_univalent D ≃ is_um_univalent D.
  Proof.
    apply weqimplimpl.
    3,4: apply isaprop_is_univalent.
    all: intro ua; apply is_univalent_from_weq; intros a b.
    all: apply (weqcomp (make_weq _ (ua a b))).
    1: apply invweq, weq_lti_iso_to_lt_iso_from_polarized.
    2: apply weq_lti_iso_to_lt_iso_from_polarized.
    all: apply (polarity_of D a).
  Qed.

  (** *** Split duploid univalence

   Let [D] be a split preduploid. The following are equivalent:

   1. The [chosen_positive_thunkable_category] and
      [chosen_negative_linear_category] of [D] are univalent.
   2. The reflexive graph whose edges are [lt_iso]s between
      same-[polarity_mapping_of] objects [is_rxgraph_univalent].
   3. For all objects [a b : D] with the same-[polarity_mapping_of],
      [id_to_lt_iso] at [a] and [b] is an equivalence.
   *)

  Definition is_split_dupl_univalent (D : split_preduploid)
    := is_univalent D⁺ᶜₜ × is_univalent D⁻ᶜₗ.

  Lemma isaprop_is_split_dupl_univalent (D : split_preduploid)
    : isaprop (is_split_dupl_univalent D).
  Proof. apply isapropdirprod; apply isaprop_is_univalent. Qed.

  Local Notation ω := (polarity_mapping_of _).

  Definition have_same_polarity {D : split_preduploid} (a b : D) : UU
    := ∑ ε, ω a = ε × ω b = ε.

  Definition have_same_polarity_refl {D : split_preduploid} (a : D)
    : have_same_polarity a a.
  Proof. now exists (ω a). Defined.

  Definition split_duploid_ob_rxgraph (D : split_preduploid) : rxgraph.
  Proof.
    use make_rxgraph.
    - exact (ob D).
    - intros a b.
      exact (have_same_polarity a b × lt_iso a b).
    - intro a.
      exact (have_same_polarity_refl a,, submm_iso_identity _ a).
  Defined.

  Definition is_split_dupl_univalent_alt (D : split_preduploid) : UU
    := ∏ (a b : D) (H : have_same_polarity a b),
      isweq (λ (p : a = b), id_to_submm_iso _lt p).

  Definition have_same_polarity_weq {D : split_preduploid} (a b : D)
    : have_same_polarity a b ≃ polarity_mapping_of D a = polarity_mapping_of D b.
  Proof.
    use weq_iso.
    - intros [ε [Ha Hb]]; induction Hb; exact Ha.
    - intros p; exact (ω b,, p,, idpath _).
    - intros [ε [Ha Hb]]; now induction Hb.
    - easy.
  Qed.

  Lemma isaprop_have_same_polarity {D : split_preduploid} (a b : D)
    : isaprop (have_same_polarity a b).
  Proof.
    apply (isofhlevelweqb 1 (have_same_polarity_weq a b)).
    apply isasetbool.
  Qed.

  (** 1 -> 2 *)
  Lemma is_split_dupl_univalent_to_rxgraph_edges_to_weq
    (D : split_preduploid)
    (ε : hpolarity) (a : D)
    (Ha : polarity_mapping_of D a = ε)
    (isε := if ε then ^⊕ω else ^⊖ω : hsubtype D)
    (Dε := if ε then D⁺ᶜₜ else D⁻ᶜₗ)
    : (edges_to (category_to_rxgraph Dε) ltac:(induction ε; exact (make_sub_ob isε a Ha)))
        ≃ edges_to (split_duploid_ob_rxgraph D) a.
  Proof.
    induction ε.
    all: apply (weqcomp (weqtotal2asstor _ _)).
    all: apply weqfibtototal.
    all: intro b; cbn.
    all: use weqbandf; [
        apply invweq;
        apply (weqcomp (have_same_polarity_weq _ _));
        exact (make_weq _ (isweqpathscomp0r _ Ha))|].
    all: intro Hb; apply invweq.
    all: exact (weq_submm_iso_z_iso _lt
                  (make_sub_ob isε b Hb)
                  (make_sub_ob isε a Ha)).
  Defined.

  Lemma is_split_dupl_univalent_to_rxgraph (D : split_preduploid)
    (ua : is_split_dupl_univalent D)
    : is_univalent (split_duploid_ob_rxgraph D).
  Proof.
    apply is_univalent_from_isaprop_edges_to.
    intro a.
    induction (_,, idpath _ : paths_from (ω a)) as [ε Ha].
    apply (isofhlevelweqf 1
             (is_split_dupl_univalent_to_rxgraph_edges_to_weq
                D ε a Ha)).
    induction ε; apply is_univalent_to_isaprop_edges_to, ua.
  Qed.

  (** 1 <- 2 *)
  Lemma is_split_dupl_univalent_from_rxgraph (D : split_preduploid)
    (ua : is_univalent (split_duploid_ob_rxgraph D))
    : is_split_dupl_univalent D.
  Proof.
    split; apply is_univalent_from_isaprop_edges_to.
    - intro a; cbn in a.
      apply (isofhlevelweqb 1
               (is_split_dupl_univalent_to_rxgraph_edges_to_weq
                  D chpositive a (sub_ob_property ^⊕ω a))).
      apply is_univalent_to_isaprop_edges_to, ua.
    - intro a; cbn in a.
      apply (isofhlevelweqb 1
               (is_split_dupl_univalent_to_rxgraph_edges_to_weq
                  D chnegative a (sub_ob_property ^⊖ω a))).
      apply is_univalent_to_isaprop_edges_to, ua.
  Qed.

  (** 2 -> 3 *)
  Lemma is_split_dupl_univalent_rxgraph_to_alt (D : split_preduploid)
    (ua : is_univalent (split_duploid_ob_rxgraph D))
    : is_split_dupl_univalent_alt D.
  Proof.
    intros a b Hab.
    use weqhomot.
    - apply (weqcomp (make_weq _ (ua a b))).
      apply (weqcomp (weqdirprodcomm _ _)).
      apply weqpr1.
      intro; apply iscontraprop1.
      + apply isaprop_have_same_polarity.
      + assumption.
    - intro p; induction p.
      reflexivity.
  Qed.

  (** 2 <- 3 *)
  Lemma is_split_dupl_univalent_rxgraph_from_alt (D : split_preduploid)
    (ua : is_split_dupl_univalent_alt D)
    : is_univalent (split_duploid_ob_rxgraph D).
  Proof.
    intros a b.
    use isweq_iso.
    - intros [Hab p].
      exact (invmap (make_weq _ (ua a b Hab)) p).
    - intros p; induction p; cbn.
      apply pathsinv0, pathsweq1.
      now apply lt_iso_eq.
    - intros [Hab p].
      apply dirprod_paths; [apply isaprop_have_same_polarity|].
      set (w := make_weq _ (ua a b Hab)).
      intermediate_path (id_to_submm_iso _lt (invmap w p)).
      2: exact (homotweqinvweq w p).
      generalize (invmap w p).
      intro e; induction e.
      now apply lt_iso_eq.
  Qed.

  Lemma is_split_dupl_univalent_to_alt (D : split_preduploid)
    (ua : is_split_dupl_univalent D)
    : is_split_dupl_univalent_alt D.
  Proof.
    apply is_split_dupl_univalent_rxgraph_to_alt.
    apply is_split_dupl_univalent_to_rxgraph.
    assumption.
  Qed.

  Lemma is_split_dupl_univalent_from_alt (D : split_preduploid)
    (ua : is_split_dupl_univalent_alt D)
    : is_split_dupl_univalent D.
  Proof.
    apply is_split_dupl_univalent_from_rxgraph.
    apply is_split_dupl_univalent_rxgraph_from_alt.
    assumption.
  Qed.

  (** *** Algebra *)

  Definition weq_id_to_lt_iso_polarized {D : split_preduploid}
    (ua : is_split_dupl_univalent D)
    {a b : D}
    (Hab : have_same_polarity a b)
    : a = b ≃ lt_iso a b
    := make_weq _ (is_split_dupl_univalent_to_alt D ua a b Hab).

  Definition lt_iso_to_id_polarized {D : split_preduploid}
    (ua : is_split_dupl_univalent D)
    {a b : D}
    (Hab : have_same_polarity a b)
    : lt_iso a b -> a = b
    := invmap (weq_id_to_lt_iso_polarized ua Hab).

  Lemma submm_isos_from_paths_polarized {D : split_preduploid}
    (ua : is_split_dupl_univalent D)
    (a b : D)
    (q : have_same_polarity a b)
    (p : a ≅{_lt} b)
    : PathPair (B:=λ b, a ≅{_lt} b)
        (@edges_from_refl (submm_rxgraph D _lt) a)
        (b,, p).
  Proof.
    transparent assert (pq : (edges_from (split_duploid_ob_rxgraph D) a)).
    { exists b; now split. }
    assert (I : PathPair (@edges_from_refl (split_duploid_ob_rxgraph D) a) pq).
    { apply total2_paths_equiv, proofirrelevance.
      apply is_univalent_to_isaprop_edges_from.
      apply is_split_dupl_univalent_to_rxgraph, ua. }
    induction I as [Haa' Hpq]; cbn in Haa', Hpq.
    exists Haa'; induction Haa'; cbn in Hpq |- *.
    apply pathsdirprodweq in Hpq.
    exact (pr2 Hpq).
  Qed.

  Lemma submm_isos_to_paths_polarized {D : split_preduploid}
    (ua : is_split_dupl_univalent D)
    (a b : D)
    (q : have_same_polarity a b)
    (p : a ≅{_lt} b)
    : PathPair (B:=λ a, a ≅{_lt} b)
        (@edges_to_refl (submm_rxgraph D _lt) b)
        (a,, p).
  Proof.
    transparent assert (pq : (edges_to (split_duploid_ob_rxgraph D) b)).
    { exists a; now split. }
    assert (I : PathPair (@edges_to_refl (split_duploid_ob_rxgraph D) b) pq).
    { apply total2_paths_equiv, proofirrelevance.
      apply is_univalent_to_isaprop_edges_to.
      apply is_split_dupl_univalent_to_rxgraph, ua. }
    induction I as [Haa' Hpq]; cbn in Haa', Hpq.
    exists Haa'; induction Haa'; cbn in Hpq |- *.
    apply pathsdirprodweq in Hpq.
    exact (pr2 Hpq).
  Qed.

End univalence_def.

(** ** Consequences of univalence *)
Section univalence_consequences.
  Lemma isaprop_is_dupl_univalent (M : unital_magmoid)
    : isaprop (is_dupl_univalent M).
  Proof. do 2 (apply impred; intro); apply isapropisweq. Qed.

  (** *** Polarity shifts are a property in single-sorted duploids *)

  Definition has_negative_shifts_alt (M : unital_magmoid) : UU
    := ∏ (a : M), ∑ (upshift : @sub_ob M ^⊖), submm_iso _l upshift a.

  Lemma has_negative_shifts_alt_weq (M : unital_magmoid)
    : has_negative_shifts M ≃ has_negative_shifts_alt M.
  Proof.
    use weq_iso.
    - intros [D H] a.
      exists (upshift' D a,, is_negative_upshift' H a).
      use make_submm_iso'.
      + exists (force' D a).
        exact (is_linear_force' H a).
      + exact (delay' H a).
      + exact (has_linear_inverse_force' H a).
    - intros S.
      use make_has_negative_shifts.
      + use make_negative_shift_data.
        * intro a; exact (pr1 (S a)).
        * intro a; exact (submm_mor_mor (pr2 (S a))).
      + use make_negative_shift_axioms.
        * intro a; exact (submm_mor_property _l _).
        * intro a; exact (sub_ob_property ^⊖ _).
        * intro a; exact (pr2 (S a)).
    - easy.
    - easy.
  Defined.

  Lemma isaprop_has_negative_shifts (M : unital_magmoid)
    (ua : is_um_univalent M)
    : isaprop (has_negative_shifts M).
  Proof.
    apply (isofhlevelweqb 1 (has_negative_shifts_alt_weq M)).
    apply impred; intro.
    apply isaprop_linear_isos_from_negative, ua.
  Qed.

  Definition has_positive_shifts_alt (M : unital_magmoid) : UU
    := ∏ (a : M), ∑ (downshift : @sub_ob M ^⊕), submm_iso _t a downshift.

  Lemma has_positive_shifts_alt_weq (M : unital_magmoid)
    : has_positive_shifts M ≃ has_positive_shifts_alt M.
  Proof.
    use weq_iso.
    - intros [D H] a.
      exists (downshift' D a,, is_positive_downshift' H a).
      use make_submm_iso'.
      + exists (wrap' D a).
        exact (is_thunkable_wrap' H a).
      + exact (unwrap' H a).
      + exact (has_thunkable_inverse_wrap' H a).
    - intros S.
      use make_has_positive_shifts.
      + use make_positive_shift_data.
        * intro a; exact (pr1 (S a)).
        * intro a; exact (submm_mor_mor (pr2 (S a))).
      + use make_positive_shift_axioms.
        * intro a; exact (submm_mor_property _t _).
        * intro a; exact (sub_ob_property ^⊕ _).
        * intro a; exact (pr2 (S a)).
    - easy.
    - easy.
  Defined.

  Lemma isaprop_has_positive_shifts (M : unital_magmoid)
    (ua : is_um_univalent M)
    : isaprop (has_positive_shifts M).
  Proof.
    apply (isofhlevelweqb 1 (has_positive_shifts_alt_weq M)).
    apply impred; intro.
    apply isaprop_thunkable_isos_to_positive, ua.
  Qed.

  Theorem isaprop_has_polarity_shifts (M : unital_magmoid) (ua : is_um_univalent M)
    : isaprop (has_polarity_shifts M).
  Proof.
    apply isapropdirprod.
    - apply isaprop_has_negative_shifts, ua.
    - apply isaprop_has_positive_shifts, ua.
  Qed.

  (** *** Polarity shifts are a property in split preduploids *)

  Lemma isaprop_linear_isos_from_negative_polarized
    {M : split_preduploid}
    (ua : is_split_dupl_univalent M)
    (b : M)
    : isaprop (∑ (a : sub_ob M ^⊖ω), a ≅{_l} b).
  Proof.
    apply invproofirrelevance.
    intros [[a Ha] e] [[a' Ha'] e'].
    transparent assert (ee' : (lt_iso a a')). {
      refine (submm_iso_incl M _l _lt _
                (subcat_iso_compose _ e (submm_iso_inv _ e'))).
      split; (intros f Hf; split;
              [ exact Hf
              | apply is_thunkable_of_negative ];
              now apply pmap_negative).
    }
    induction (submm_isos_from_paths_polarized ua _ _
                 (chnegative,, Ha,, Ha') ee') as [Haa' Hee'].
    apply submm_iso_eq_mor in Hee'.
    cbn in Haa', Hee'.
    clear ee'; cbn in *.
    induction Haa'; cbn in Hee'.
    induction (proofirrelevance_hProp (^⊖ω a) Ha Ha').
    apply pair_path_in2, (subcat_iso_eq _l).
    apply subcat_iso_eq_from_identity_right.
    exact (!Hee').
  Qed.

  Lemma isaprop_thunkable_isos_from_positive_polarized
    {M : split_preduploid}
    (ua : is_split_dupl_univalent M)
    (b : M)
    : isaprop (∑ (a : sub_ob M ^⊕ω), b ≅{_t} a).
  Proof.
    apply invproofirrelevance.
    intros [[a Ha] e] [[a' Ha'] e'].
    transparent assert (ee' : (lt_iso a a')). {
      refine (submm_iso_incl M _t _lt _
                (subcat_iso_compose _ (submm_iso_inv _ e) e')).
      split; (intros f Hf; split;
              [ apply is_linear_of_positive
              | exact Hf ];
              now apply pmap_positive).
    }
    induction (submm_isos_from_paths_polarized ua _ _
                 (chpositive,, Ha,, Ha') ee') as [Haa' Hee'].
    apply submm_iso_eq_mor in Hee'.
    cbn in Haa', Hee'.
    clear ee'; cbn in *.
    induction Haa'; cbn in Hee'.
    induction (proofirrelevance_hProp (^⊕ω a) Ha Ha').
    apply pair_path_in2, (subcat_iso_eq _t).
    apply pathsinv0, subcat_iso_eq_from_identity_left.
    exact (!Hee').
  Qed.

  Definition has_split_negative_shifts_alt
    (M : unital_magmoid) (ω : M -> hpolarity) : UU
    := ∏ (a : M), ∑ (upshift : @sub_ob M (ish_chnegative' ω)),
      submm_iso _l upshift a.

  Lemma has_split_negative_shifts_alt_weq
    (M : unital_magmoid) (ω : polarity_mapping M)
    : has_split_negative_shifts M ω ≃ has_split_negative_shifts_alt M ω.
  Proof.
    intermediate_weq (∑ (S : has_negative_shifts_alt M),
                       ∏ (a : M), ish_chnegative' ω (pr1 (S a))). {
      use weqbandf.
      - apply has_negative_shifts_alt_weq.
      - intro S; exact (idweq (pmap_respects_negative_shifts S ω)).
    }
    eapply weqcomp. {
      apply invweq,
        (sec_total2_distributivity
           (λ (a : M) (shift : ∑ upshift : sub_ob M ^⊖,
                    submm_iso _l upshift a),
             ish_chnegative' ω (pr1 shift))).
    }
    apply weqonsecfibers; intro a.
    intermediate_weq (∑ (upshift : sub_ob M ^⊖),
                       submm_iso _l upshift a × ish_chnegative' ω upshift).
    { apply invweq, totalAssociativity. }
    eapply weqcomp.
    { apply weqfibtototal; intro. apply weqdirprodcomm. }
    intermediate_weq (∑ (upshift : ∑ (x : sub_ob M ^⊖), ish_chnegative' ω x),
                       submm_iso _l (pr1 upshift) a).
    { apply totalAssociativity. }
    use weqbandf. {
      intermediate_weq (∑ (x : M), ish_negative x × ish_chnegative' ω x).
      { apply invweq, totalAssociativity. }
      apply weqfibtototal; intro x.
      apply (weqcomp (weqdirprodcomm _ _)).
      apply weqpr1; intro H.
      apply iscontraprop1.
      - apply propproperty.
      - apply (pmap_negative' ω), H.
    }
    intros upshift.
    exact (idweq _).
  Defined.

  Lemma isaprop_has_split_negative_shifts (D : split_preduploid)
    (ua : is_split_dupl_univalent D)
    : isaprop (has_split_negative_shifts D D).
  Proof.
    apply (isofhlevelweqb 1 (has_split_negative_shifts_alt_weq D D)).
    apply impred; intro.
    apply isaprop_linear_isos_from_negative_polarized, ua.
  Qed.

  Definition has_split_positive_shifts_alt
    (M : unital_magmoid) (ω : M -> hpolarity) : UU
    := ∏ (a : M), ∑ (downshift : @sub_ob M (ish_chpositive' ω)),
      submm_iso _t a downshift.

  Lemma has_split_positive_shifts_alt_weq
    (M : unital_magmoid) (ω : polarity_mapping M)
    : has_split_positive_shifts M ω ≃ has_split_positive_shifts_alt M ω.
  Proof.
    intermediate_weq (∑ (S : has_positive_shifts_alt M),
                       ∏ (a : M), ish_chpositive' ω (pr1 (S a))). {
      use weqbandf.
      - apply has_positive_shifts_alt_weq.
      - intro S; exact (idweq (pmap_respects_positive_shifts S ω)).
    }
    eapply weqcomp. {
      apply invweq,
        (sec_total2_distributivity
           (λ (a : M) (shift : ∑ downshift : sub_ob M ^⊕,
                    submm_iso _t a downshift),
             ish_chpositive' ω (pr1 shift))).
    }
    apply weqonsecfibers; intro a.
    intermediate_weq (∑ (downshift : sub_ob M ^⊕),
                       submm_iso _t a downshift × ish_chpositive' ω downshift).
    { apply invweq, totalAssociativity. }
    eapply weqcomp.
    { apply weqfibtototal; intro. apply weqdirprodcomm. }
    intermediate_weq (∑ (downshift : ∑ (x : sub_ob M ^⊕), ish_chpositive' ω x),
                       submm_iso _t a (pr1 downshift)).
    { apply totalAssociativity. }
    use weqbandf. {
      intermediate_weq (∑ (x : M), ish_positive x × ish_chpositive' ω x).
      { apply invweq, totalAssociativity. }
      apply weqfibtototal; intro x.
      apply (weqcomp (weqdirprodcomm _ _)).
      apply weqpr1; intro H.
      apply iscontraprop1.
      - apply propproperty.
      - apply (pmap_positive' ω), H.
    }
    intros downshift.
    exact (idweq _).
  Defined.

  Lemma isaprop_has_split_positive_shifts (D : split_preduploid)
    (ua : is_split_dupl_univalent D)
    : isaprop (has_split_positive_shifts D D).
  Proof.
    apply (isofhlevelweqb 1 (has_split_positive_shifts_alt_weq D D)).
    apply impred; intro.
    apply isaprop_thunkable_isos_from_positive_polarized, ua.
  Qed.

  Lemma isaprop_has_split_shifts (D : split_preduploid)
    (ua : is_split_dupl_univalent D)
    : isaprop (∑ (S : has_polarity_shifts D), pmap_respects_shifts S D).
  Proof.
    apply (isofhlevelweqb 1 (Y:=has_split_negative_shifts D D
                                  × has_split_positive_shifts D D)). {
      use weq_iso.
      - intros [[A B] [HA HB]].
        exact ((A,, HA),, (B,, HB)).
      - intros [[A HA] [B HB]].
        exact ((A,, B),, (HA,, HB)).
      - easy.
      - easy.
    }
    apply isapropdirprod.
    - apply isaprop_has_split_negative_shifts, ua.
    - apply isaprop_has_split_positive_shifts, ua.
  Qed.

End univalence_consequences.

(** ** Characterizations of univalence *)

Section characterizations.
  Context (D : preduploid).
  (** The following are equivalent:
      1. [D] is a univalent duploid
      2. [linear_and_thunkable_category D] is a univalent category
      3. [positive_thunkable_category D] and [negative_linear_category D] are both univalent categories *)

  (** 1 -> 2 *)
  Lemma duploid_to_lt_cat_rxgraph_iso
    : rxgraph_iso (category_to_rxgraph (D ₗₜ)) (duploid_to_rxgraph D).
  Proof.
    use make_rxgraph_iso.
    - apply idweq.
    - intros a b.
      apply invweq, weq_submm_iso_z_iso.
    - intro a.
      now apply lt_iso_eq.
  Defined.

  Lemma is_dupl_univalent_to_lt_cat
    (H : is_dupl_univalent D) : Univalence.is_univalent (D ₗₜ).
  Proof.
    exact (is_univalent_rxgraph_iso_b _ _
             duploid_to_lt_cat_rxgraph_iso
             H).
  Qed.

  (** 2 -> 1 *)
  Lemma is_dupl_univalent_from_lt_cat
    (H : Univalence.is_univalent (D ₗₜ)) : is_dupl_univalent D.
  Proof.
    exact (is_univalent_rxgraph_iso_f _ _
             duploid_to_lt_cat_rxgraph_iso
             H).
  Qed.

  (** 2 -> 3.a *)
  Lemma is_univalent_lt_cat_to_pos_t_cat
    (H : Univalence.is_univalent (D ₗₜ)) : Univalence.is_univalent (D ⁺ₜ).
  Proof.
    intros a b.
    use weqhomot.
    - induction a as [a Ha], b as [b Hb].
      intermediate_weq (a = b); [apply path_sigma_hprop, propproperty|].
      intermediate_weq (z_iso (C:=linear_and_thunkable_category D) a b);
        [exact (make_weq _ (H a b))|].
      apply invweq.
      apply (weq_ff_functor_on_z_iso
               (fully_faithful_positive_thunkable_to_linear_and_thunkable_category D)).
    - intro p.
      apply z_iso_eq, submm_mor_eq.
      now induction p.
  Qed.

  (** 2 -> 3.b *)
  Lemma is_univalent_lt_cat_to_neg_l_cat
    (H : Univalence.is_univalent (D ₗₜ)) : Univalence.is_univalent (D ⁻ₗ).
  Proof.
    intros a b.
    use weqhomot.
    - induction a as [a Ha], b as [b Hb].
      intermediate_weq (a = b); [apply path_sigma_hprop, propproperty|].
      intermediate_weq (z_iso (C:=linear_and_thunkable_category D) a b);
        [exact (make_weq _ (H a b))|].
      apply invweq.
      apply (weq_ff_functor_on_z_iso
               (fully_faithful_negative_linear_to_linear_and_thunkable_category D)).
    - intro p.
      apply z_iso_eq, submm_mor_eq.
      now induction p.
  Qed.

  (* 3 -> 2 *)
  Lemma is_univalent_lt_cat_from_polarized
    (Hpositive : Univalence.is_univalent (D⁺ₜ))
    (Hnegative : Univalence.is_univalent (D⁻ₗ))
    : Univalence.is_univalent (D ₗₜ).
  Proof.
    apply (is_univalent_from_isaprop_edges_from (category_to_rxgraph (D ₗₜ))).
    intro a.
    isaprop_goal Hprop; [apply isapropisaprop|].
    refine (squash_to_prop (polarity_of D a) Hprop (λ Ha, _)).
    induction Ha as [Ha | Ha].
    1: set (C := D⁻ₗ).                           2: set (C := D⁺ₜ).
    1: set (HC := Hnegative).                    2: set (HC := Hpositive).
    1: set (is_p := @is_negative D).             2: set (is_p := @is_positive D).
    all: set (a' := a,,Ha : C).
    all: use (isofhlevelweqb 1 (Y:=edges_from (category_to_rxgraph C) a'));
      [|exact (is_univalent_to_isaprop_edges_from (category_to_rxgraph C) HC _)].
    all: eapply weqcomp; [|apply weqtotal2asstol].
    all: use weqbandf; [exact (idweq D)|]; intro b; cbn in b |- *.
    all: intermediate_weq (∑ _ : z_iso (C:=D ₗₜ) a b, is_p b).
    1,3:   apply invweq, weqpr1; intro e.
    1,2:   apply iscontraprop1.
    1:     apply isaprop_is_negative.            2: apply isaprop_is_positive.
    1:     refine (is_negative_of_lt_iso _ Ha).  2: refine (is_positive_of_lt_iso _ Ha).
    1,2:   apply weq_submm_iso_z_iso, e.
    all: eapply weqcomp; [apply weqdirprodcomm|].
    all: use weqbandf; [exact (idweq _)|]; intro Hb; cbn.
    all: apply invweq.
    1: apply (weq_ff_functor_on_z_iso (fully_faithful_negative_linear_to_linear_and_thunkable_category D)).
    1: apply (weq_ff_functor_on_z_iso (fully_faithful_positive_thunkable_to_linear_and_thunkable_category D)).
  Qed.

  (* 3 -> 1 *)
  Lemma is_dupl_univalent_from_polarized
    (Hpositive : Univalence.is_univalent (D⁺ₜ))
    (Hnegative : Univalence.is_univalent (D⁻ₗ))
    : is_dupl_univalent D.
  Proof.
    apply is_dupl_univalent_from_lt_cat.
    apply is_univalent_lt_cat_from_polarized.
    all: assumption.
  Qed.

End characterizations.

(** ** Split duploids and univalence *)
Section split_duploids.

  Lemma neg_is_dupl_univalent_if_split (D : split_duploid)
    (a : D) (Hpositive : is_positive a) (Hnegative : is_negative a)
    : ¬is_dupl_univalent D.
  Proof.
    intro ua.
    enough (Heq : (⇑a : D) = ⇓a). {
      apply (maponpaths (polarity_mapping_of D)) in Heq.
      apply nopathsfalsetotrue.
      refine (_ @ Heq @ _).
      - apply pathsinv0, pmap_upshift.
      - apply pmap_downshift.
    }
    use (submm_iso_to_id _ _ ua).
    apply (subcat_iso_compose _lt (b:=a)).
    - apply (lt_iso_upshift_of_negative a Hnegative).
    - apply (lt_iso_downshift_of_positive a Hpositive).
  Qed.

End split_duploids.
