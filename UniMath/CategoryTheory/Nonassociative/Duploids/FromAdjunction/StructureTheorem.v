(********************************************************************************

 The Structure Theorem for Duploids

 Author: B. Szilvasy
 February–October 2026

 We prove that all duploids are equivalent to the envelope duploid over the
 adjunction [⇑ ⊣ ⇓] of that duploid.  We do not yet provide a correspondence
 between any sort of 1-cells between adjunctions or duploids, nor indeed between
 any sort of 2-cells either.

 Contents:
 1. Every duploid is (weakly) equivalent to an envelope duploid
 1.1. Definition of the equivalence
 1.2. Proof of being an equivalence

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.ObliqueMor.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.Envelope.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.EqualizingRequirement.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.
Local Open Scope oblique_mor.

(** ** Every duploid is (weakly) equivalent to an envelope duploid *)

Section envelope_equiv.
  Context (D : duploid).
  Let θ := adjunction_neg_l_to_pos_t D.
  Let D' := envelope_duploid θ.

  (** *** Definition of the equivalence *)

  Definition duploid_into_envelope_oblique_mor (a : ob D) : D⁻ₗ⟦⇑⇓a, ⇑a⟧.
  Proof.
    apply (#upshift_l_to_neg_l).
    exists (unwrap a).
    apply is_linear_unwrap.
  Defined.

  Definition duploid_into_envelope_oblique_mor' (a : ob D) : D⁺ₜ⟦⇓a, ⇓⇑a⟧.
  Proof.
    apply (#downshift_t_to_pos_t).
    exists (delay a).
    apply is_thunkable_delay.
  Defined.

  Lemma duploid_into_envelope_oblique_mor_eq (a : ob D)
    : φ_adj θ (duploid_into_envelope_oblique_mor a)
      = duploid_into_envelope_oblique_mor' a.
  Proof.
    apply submm_mor_eq; cbn.
    etrans; [apply assoc'_negative, (⇑_)|].
    etrans; [apply cancel_precomposition, pathsinv0, wrap_natural|].
    etrans; [apply assoc_negative, (⇑_)|].
    etrans; [apply cancel_postcomposition, pathsinv0, delay_natural|].
    etrans; [apply assoc'_thunkable, (unwrap _)|].
    reflexivity.
  Qed.

  Definition duploid_into_envelope_preob (a : ob D) : envelope_preob θ.
  Proof.
    apply (make_envelope_preob θ ⇓a ⇑a).
    use make_oblique_mor_forward.
    - exact (duploid_into_envelope_oblique_mor a).
    - exact (duploid_into_envelope_oblique_mor' a).
    - apply duploid_into_envelope_oblique_mor_eq.
  Defined.

  Definition envelope_on_shifts_chosen_negative_of_is_negative (a : ob D)
    (Hn : is_negative a)
    : envelope_chosen_negative θ (duploid_into_envelope_preob a).
  Proof.
    use make_is_z_isomorphism.
    - cbn.
      apply (#downshift_t_to_pos_t).
      exists (force a).
      apply is_thunkable_force_of_negative, Hn.
    - abstract (
          use make_is_inverse_in_precat;
          first [
              apply submm_mor_eq; cbn;
              etrans; [apply pathsinv0, downshiftf_comp, is_thunkable_delay|];
              etrans; [|apply downshiftf_id];
              apply maponpaths, delay_force_id
            | apply submm_mor_eq; cbn;
              etrans; [apply pathsinv0, downshiftf_comp, is_thunkable_force_of_negative, Hn|];
              etrans; [|apply downshiftf_id];
              apply maponpaths, force_delay_id]).
  Defined.

  Definition envelope_on_shifts_chosen_positive_of_is_positive (a : ob D)
    (Hp : is_positive a)
    : envelope_chosen_positive θ (duploid_into_envelope_preob a).
  Proof.
    use make_is_z_isomorphism.
    - cbn.
      apply (#upshift_l_to_neg_l).
      exists (wrap a).
      apply is_linear_wrap_of_positive, Hp.
    - abstract (
          use make_is_inverse_in_precat;
          first [
              apply submm_mor_eq; cbn;
              etrans; [apply pathsinv0, upshiftf_comp, is_linear_unwrap|];
              etrans; [|apply upshiftf_id];
              apply maponpaths, wrap_unwrap_id
            | apply submm_mor_eq; cbn;
              etrans; [apply pathsinv0, upshiftf_comp, is_linear_wrap_of_positive, Hp|];
              etrans; [|apply upshiftf_id];
              apply maponpaths, unwrap_wrap_id]).
  Defined.

  Definition duploid_into_envelope_envelope_polarization (a : ob D)
    : envelope_polarization θ (duploid_into_envelope_preob a).
    apply (has_polarity_rec (polarity_of D a)).
    - apply isaprop_envelope_polarization.
    - intro Hn.
      apply hinhpr, ii1.
      apply envelope_on_shifts_chosen_negative_of_is_negative, Hn.
    - intro Hp.
      apply hinhpr, ii2.
      apply envelope_on_shifts_chosen_positive_of_is_positive, Hp.
  Defined.

  Definition duploid_into_envelope_ob (a : ob D) : envelope_ob θ.
  Proof.
    use make_envelope_ob.
    - exact (duploid_into_envelope_preob a).
    - exact (duploid_into_envelope_envelope_polarization a).
  Defined.

  Lemma is_epi_wrap (a z : D) (g h : ⇓a --> z)
    : wrap a · g = wrap a · h -> g = h.
  Proof.
    intro H.
    apply (maponpaths (λ x, unwrap a · x)) in H.
    refine (_ @ H @ _).
    - rewrite (assoc_thunkable (unwrap a) ummsolve).
      apply pathsinv0, magmoid_remove_id_left, unwrap_wrap_id.
    - rewrite (assoc_thunkable (unwrap a) ummsolve).
      apply magmoid_remove_id_left, unwrap_wrap_id.
  Qed.

  Definition duploid_into_envelope_envelope_mor (a b : ob D)
    (f : a --> b)
    : envelope_mor θ
        (duploid_into_envelope_ob a)
        (duploid_into_envelope_ob b).
  Proof.
    use make_oblique_mor_forward.
    - apply (#upshift_l_to_neg_l).
      exists (positive_lift f).
      apply is_linear_of_positive, (⇓a).
    - apply (#downshift_t_to_pos_t).
      exists (negative_lift f).
      apply is_thunkable_of_negative, (⇑b).
    - abstract (
          apply submm_mor_eq; cbn;
          etrans; [apply assoc'_negative, (⇑_)|];
          etrans; [apply cancel_precomposition, pathsinv0, wrap_natural|];
          etrans; [apply assoc_negative, (⇑_)|];
          etrans; [apply cancel_postcomposition, pathsinv0, delay_natural|];
          apply is_epi_wrap;
          etrans; [apply assoc_thunkable, (wrap _)|];
          etrans; [apply cancel_postcomposition, assoc_thunkable, (wrap _)|];
          etrans; [apply cancel_postcomposition, cancel_postcomposition, positive_lift_property|];
          etrans; [|apply wrap_natural];
          reflexivity).
  Defined.

  Definition duploid_into_envelope_data
    : functor_data D D'.
  Proof.
    use make_functor_data.
    - apply duploid_into_envelope_ob.
    - apply duploid_into_envelope_envelope_mor.
  Defined.

  Definition duploid_into_envelope_is_functor
    : is_functor duploid_into_envelope_data.
  Proof.
    use make_is_functor.
    - intro a.
      apply oblique_mor_negative_path, submm_mor_eq; cbn.
      apply maponpaths, magmoid_id_right.
    - intros a b c f g.
      cbn.
      unfold duploid_into_envelope_envelope_polarization.
      pattern (polarity_of D b).
      apply (has_polarity_rec_dep (polarity_of D b)).
      + intro; apply isaset_oblique_mor.
      + intro Hn.
        apply oblique_mor_positive_path.
        apply submm_mor_eq; cbn.
        etrans; [|apply cancel_postcomposition, downshiftf_comp,
                  is_thunkable_of_negative, (⇑_)].
        etrans; [|apply downshiftf_comp, is_thunkable_of_negative, Hn].
        apply maponpaths.
        apply pathsinv0, negative_lift_unique.
        etrans; [apply cancel_postcomposition, cancel_postcomposition, negative_lift_property|].
        etrans; [apply assoc'_negative, Hn|].
        apply cancel_precomposition, negative_lift_property.
      + intro Hp.
        apply oblique_mor_negative_path, submm_mor_eq; cbn.
        etrans; [|apply cancel_precomposition, upshiftf_comp,
                  is_linear_of_positive, (⇓_)].
        etrans; [|apply upshiftf_comp, is_linear_of_positive, Hp].
        apply maponpaths.
        apply pathsinv0, positive_lift_unique.
        etrans; [apply cancel_precomposition, cancel_precomposition, positive_lift_property|].
        etrans; [apply assoc_positive, Hp|].
        apply cancel_postcomposition, positive_lift_property.
  Qed.

  Definition duploid_into_envelope : D ⟶ D'
    := make_functor _ duploid_into_envelope_is_functor.
  Notation ι := duploid_into_envelope.

  (** *** Proof of being an equivalence *)

  Lemma fully_faithful_duploid_into_envelope
    : fully_faithful duploid_into_envelope.
  Proof.
    intros a b.
    use weqhomot.
    - intermediate_weq (D ⟦⇓a, b⟧).
      { exists positive_lift; apply isweq_positive_lift. }
      intermediate_weq (D ₗ⟦⇓a, b⟧).
      { apply weq_make_submm_mor; intro.
        apply is_linear_of_positive, (⇓_). }
      intermediate_weq (D⁻ₗ⟦⇑⇓a, ⇑b⟧).
      { apply (weq_from_fully_faithful
                 (fully_faithful_from_equivalence _ _ _
                    (adj_equivalence_of_cats_inv
                       (equiv_negative_linear_to_linear_category D)))
                 (⇓a) b). }
      apply invweq; exact (weq_oblique_mor_negative θ _ _).
    - abstract (intros f; apply oblique_mor_negative_path; now apply submm_mor_eq).
  Defined.

  Definition duploid_into_envelope_negative_fibre
    (b : envelope_ob θ) (Hn : is_negative b)
    : submm_fibre ι _lt b.
  Proof.
    set (a := envelope_negative_ob θ b); cbn in a.
    exists a.
    refine (subcat_iso_compose _lt (b:=⇑(ι a)) _ _). {
      apply submm_iso_inv, lt_iso_upshift_of_negative.
      apply is_negative_of_envelope_chosen_negative.
      apply envelope_on_shifts_chosen_negative_of_is_negative.
      apply a.
    }
    refine (subcat_iso_compose _lt (b:=⇑b) _ _). {
      enough (e : z_iso (C:=D⁻ₗ) (π⊖ (ι a : envelope_ob _)) (π⊖ b)).
      { apply weq_submm_iso_z_iso.
        exact (functor_on_z_iso (negative_to_envelope_duploid θ) e). }
      apply weq_submm_iso_z_iso.
      change (lt_iso (⇑(a : D)) a).
      apply lt_iso_upshift_of_negative, a.
    }
    apply lt_iso_upshift_of_negative, Hn.
  Defined.

  Definition duploid_into_envelope_positive_fibre
    (b : envelope_ob θ) (Hp : is_positive b)
    : submm_fibre ι _lt b.
  Proof.
    set (a := envelope_positive_ob θ b); cbn in a.
    exists a.
    refine (subcat_iso_compose _lt (b:=⇓(ι a)) _ _). {
      apply lt_iso_downshift_of_positive.
      apply is_positive_of_envelope_chosen_positive.
      apply envelope_on_shifts_chosen_positive_of_is_positive.
      apply a.
    }
    refine (subcat_iso_compose _lt (b:=⇓b) _ _). {
      enough (e : z_iso (C:=D⁺ₜ) (π⊕ (ι a : envelope_ob _)) (π⊕ b)).
      { apply weq_submm_iso_z_iso.
        exact (functor_on_z_iso (positive_to_envelope_duploid θ) e). }
      apply weq_submm_iso_z_iso.
      change (lt_iso (⇓(a : D)) a).
      apply submm_iso_inv, lt_iso_downshift_of_positive, a.
    }
    apply submm_iso_inv, lt_iso_downshift_of_positive, Hp.
  Defined.

  Lemma eso_duploid_into_envelope
    : submm_essentially_surjective ι _lt.
  Proof.
    intro a; cbn in a.
    apply (has_polarity_rec (polarity_of D' a)).
    - apply isapropishinh.
    - intro Hnegative; apply hinhpr.
      apply duploid_into_envelope_negative_fibre, Hnegative.
    - intro Hpositive; apply hinhpr.
      apply duploid_into_envelope_positive_fibre, Hpositive.
  Qed.

  Lemma split_eso_duploid_into_envelope_from_LEM (lem : LEM)
    : submm_split_essentially_surjective ι _lt.
  Proof.
    intros a; cbn in a.
    induction (lem (ish_negative a)) as [Hnegative | Hpositive].
    - apply duploid_into_envelope_negative_fibre, Hnegative.
    - apply (λ x, hinhuniv (invmap (weqii2withneg (ish_positive _) x)) (polarity_of D' a)) in Hpositive.
      apply duploid_into_envelope_positive_fibre, Hpositive.
  Qed.

  Lemma is_weak_equiv_duploid_into_envelope
    : is_submm_weak_equiv ι _lt.
  Proof.
    split.
    - exact fully_faithful_duploid_into_envelope.
    - exact eso_duploid_into_envelope.
  Defined.

  Lemma is_strong_equiv_duploid_into_envelope_from_LEM (lem : LEM)
    : is_submm_strong_equiv ι _lt.
  Proof.
    split.
    - exact fully_faithful_duploid_into_envelope.
    - exact (split_eso_duploid_into_envelope_from_LEM lem).
  Defined.

  Theorem weak_equiv_duploid_into_envelope
    : submm_weak_equiv D D' _lt.
  Proof.
    exact (make_submm_weak_equiv _ _ _ ι
             is_weak_equiv_duploid_into_envelope).
  Defined.

End envelope_equiv.
