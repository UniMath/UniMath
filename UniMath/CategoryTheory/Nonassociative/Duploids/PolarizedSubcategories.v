(********************************************************************************

 Polarized Subcategories in Duploids

 Author: B. Szilvasy
 January–October 2026

 Contents:
 1. Syntactic polarized subcategories
 2. Inclusion functors
 3. Equivalences
 3.1. Equivalence of syntactic and semantic categories
 3.2. Equivalence of (un)polarized subcategories

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** Syntactic polarized subcategories *)

Section syntactic_subcategories.
  Context (D : split_preduploid).

  Definition syn_positive_category : category := associative_submagmoid_carrier D ^⊕ω _l.
  Definition syn_negative_category : category := associative_submagmoid_carrier D ^⊖ω _t.
  Definition syn_positive_thunkable_category : category := associative_submagmoid_carrier D ^⊕ω _lt.
  Definition syn_negative_linear_category : category := associative_submagmoid_carrier D ^⊖ω _lt.

  Definition weq_syn_positive_mor {a b : sub_ob D ^⊕ω}
    : D⟦a, b⟧ ≃ D∣_l∣⟦a, b⟧.
  Proof.
    apply weq_make_submm_mor; intro f.
    apply is_linear_of_positive, pmap_positive.
    exact (sub_ob_property _ a).
  Defined.

  Definition weq_syn_positive_thunkable_mor {a b : sub_ob D ^⊕ω}
    : D∣_t∣⟦a, b⟧ ≃ D∣_lt∣⟦a, b⟧.
  Proof.
    apply weq_submm_mor_incl; intro f.
    apply dirprod_with_contr_l.
    apply iscontraprop1.
    - apply propproperty.
    - apply is_linear_of_positive, pmap_positive.
      exact (sub_ob_property _ a).
  Defined.

  Definition weq_syn_positive_z_iso (a b : sub_ob D ^⊕ω)
    : z_iso a b ≃ a ≅{_l} b.
  Proof.
    apply (weqcomp (invweq (weq_trivial_submm_iso_z_iso a b))).
    apply weq_submm_iso_incl;
      apply submm_includes_in_to_at_sym; clear a b.
    - intros a b f H.
      apply is_linear_of_positive, pmap_positive.
      exact (sub_ob_property _ a).
    - easy.
  Defined.

  Definition weq_syn_positive_lt_iso (a b : sub_ob D ^⊕ω)
    : a ≅{_t} b ≃ a ≅{_lt} b.
  Proof.
    apply weq_submm_iso_incl;
      apply submm_includes_in_to_at_sym; clear a b.
    - intros a b f H.
      split; solve [exact H|apply is_linear_of_positive, pmap_positive, (sub_ob_property ^⊕ω)].
    - intros a b f H; apply H.
  Defined.

  Definition weq_syn_negative_mor {a b : sub_ob D ^⊖ω}
    : D⟦a, b⟧ ≃ D∣_t∣⟦a, b⟧.
  Proof.
    apply weq_make_submm_mor; intro f.
    apply is_thunkable_of_negative.
    apply pmap_negative.
    exact (sub_ob_property _ b).
  Defined.

  Definition weq_syn_negative_linear_mor {a b : sub_ob D ^⊖ω}
    : D∣_l∣⟦a, b⟧ ≃ D∣_lt∣⟦a, b⟧.
  Proof.
    apply weq_submm_mor_incl; intro f.
    apply dirprod_with_contr_r.
    apply iscontraprop1.
    - apply propproperty.
    - apply is_thunkable_of_negative.
      apply pmap_negative.
      exact (sub_ob_property _ b).
  Defined.

  Definition weq_syn_negative_z_iso (a b : sub_ob D ^⊖ω)
    : z_iso a b ≃ a ≅{_t} b.
  Proof.
    apply (weqcomp (invweq (weq_trivial_submm_iso_z_iso a b))).
    apply weq_submm_iso_incl;
      apply submm_includes_in_to_at_sym; clear a b.
    - intros a b f H.
      apply is_thunkable_of_negative, pmap_negative.
      exact (sub_ob_property _ b).
    - easy.
  Defined.

  Definition weq_syn_negative_lt_iso (a b : sub_ob D ^⊖ω)
    : a ≅{_l} b ≃ a ≅{_lt} b.
  Proof.
    apply weq_submm_iso_incl;
      apply submm_includes_in_to_at_sym; clear a b.
    - intros a b f H.
      split; solve [exact H|apply is_thunkable_of_negative, pmap_negative, (sub_ob_property ^⊖ω)].
    - intros a b f H; apply H.
  Defined.

End syntactic_subcategories.

Notation "D '⁺ᶜ'" := (syn_positive_category D) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ *)
Notation "D '⁻ᶜ'" := (syn_negative_category D) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ *)
Notation "D '⁺ᶜₜ'" := (syn_positive_thunkable_category D) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ \_t *)
Notation "D '⁻ᶜₗ'" := (syn_negative_linear_category D) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ \_l *)

(** ** Inclusion functors *)

Section inclusions.
  Context (D : split_preduploid).

  (** Direct inclusions *)
  Definition syn_positive_to_linear_category : D⁺ᶜ ⟶ D ₗ
    := submm_into_wide_incl D ^⊕ω _l.
  Definition syn_positive_thunkable_to_linear_and_thunkable_category : D⁺ᶜₜ ⟶ D ₗₜ
    := submm_into_wide_incl D ^⊕ω _lt.
  Definition syn_positive_thunkable_to_positive_category : D⁺ᶜₜ ⟶ D⁺ᶜ
    := wide_submm_incl _
         (full_subcategory_promote D ^⊕ω _lt)
         (full_subcategory_promote D ^⊕ω _l)
         (λ a b f, pr1).

  Definition syn_negative_to_thunkable_category : D⁻ᶜ ⟶ D ₜ
    := submm_into_wide_incl D ^⊖ω _t.
  Definition syn_negative_linear_to_linear_and_thunkable_category : D⁻ᶜₗ ⟶ D ₗₜ
    := submm_into_wide_incl D ^⊖ω _lt.
  Definition syn_negative_linear_to_negative_category : D⁻ᶜₗ ⟶ D⁻ᶜ
    := wide_submm_incl _
         (full_subcategory_promote D ^⊖ω _lt)
         (full_subcategory_promote D ^⊖ω _t)
         (λ a b f, pr2).

  (** Maps into the semantics subcategories *)
  Definition syn_positive_to_sem_category : D⁺ᶜ ⟶ D⁺
    := submm_into_other_incl D ^⊕ω ^⊕ _l _l (λ a, pmap_positive a) (λ _ _ _ H, H).
  Definition syn_positive_thunkable_to_sem_category : D⁺ᶜₜ ⟶ D⁺ₜ
    := submm_into_other_incl D ^⊕ω ^⊕ _lt _lt (λ a, pmap_positive a) (λ _ _ _ H, H).
  Definition syn_negative_to_sem_category : D⁻ᶜ ⟶ D⁻
    := submm_into_other_incl D ^⊖ω ^⊖ _t _t (λ a, pmap_negative a) (λ _ _ _ H, H).
  Definition syn_negative_linear_to_sem_category : D⁻ᶜₗ ⟶ D⁻ₗ
    := submm_into_other_incl D ^⊖ω ^⊖ _lt _lt (λ a, pmap_negative a) (λ _ _ _ H, H).

End inclusions.

(** ** Equivalences *)

Section equivalences.

  (** *** Equivalence of syntactic and semantic categories *)

  (* D⁺ᶜ ≅ D⁺ *)
  Theorem equiv_syn_positive_to_sem_category (D : split_duploid)
    : adj_equivalence_of_cats (syn_positive_to_sem_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_submm_into_other_incl.
      exact (λ _ _ _ H, H).
    - intro a; cbn in a.
      use tpair.
      + exact (chpositive_downshift a).
      + apply weq_submm_iso_z_iso.
        change (⇓a ≅{_l} a).
        apply (weq_positive_z_iso D ⇓a a).
        eapply submm_iso_to_plain_z_iso.
        exact (unwrap a).
  Defined.

  (* D⁻ᶜ ≅ D⁻ *)
  Theorem equiv_syn_negative_to_sem_category (D : split_duploid)
    : adj_equivalence_of_cats (syn_negative_to_sem_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_submm_into_other_incl.
      exact (λ _ _ _ H, H).
    - intro a; cbn in a.
      use tpair.
      + exact (chnegative_upshift a).
      + apply weq_submm_iso_z_iso.
        change (⇑a ≅{_t} a).
        apply (weq_negative_z_iso D ⇑a a).
        eapply submm_iso_to_plain_z_iso.
        exact (force a).
  Defined.

  (* D⁺ᶜₜ ≅ D⁺ₜ *)
  Theorem equiv_syn_positive_thunkable_to_sem_category (D : split_duploid)
    : adj_equivalence_of_cats (syn_positive_thunkable_to_sem_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_submm_into_other_incl.
      exact (λ _ _ _ H, H).
    - intro a; cbn in a.
      use tpair.
      + exact (chpositive_downshift a).
      + apply weq_submm_iso_z_iso.
        change (⇓a ≅{_lt} a).
        apply (weq_positive_lt_iso D ⇓a a).
        exact (unwrap a).
  Defined.

  (* D⁻ᶜₗ ≅ D⁻ₗ *)
  Theorem equiv_syn_negative_linear_to_sem_category (D : split_duploid)
    : adj_equivalence_of_cats (syn_negative_linear_to_sem_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_submm_into_other_incl.
      exact (λ _ _ _ H, H).
    - intro a; cbn in a.
      use tpair.
      + exact (chnegative_upshift a).
      + apply weq_submm_iso_z_iso.
        change (⇑a ≅{_lt} a).
        apply (weq_negative_lt_iso D ⇑a a).
        exact (force a).
  Defined.

  (** *** Equivalence of (un)polarized subcategories *)

  (* D⁺ₜ ≅ Dₜ *)
  Theorem equiv_positive_thunkable_to_thunkable_category (D : duploid)
    : adj_equivalence_of_cats (positive_thunkable_to_thunkable_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_positive_thunkable_to_thunkable_category.
    - intro a; cbn in a.
      use tpair.
      + exact ⇓a.
      + apply weq_submm_iso_z_iso.
        change (⇓a ≅{_t} a).
        exact (unwrap a).
  Defined.

  (* D⁻ₗ ≅ Dₗ *)
  Theorem equiv_negative_linear_to_linear_category (D : duploid)
    : adj_equivalence_of_cats (negative_linear_to_linear_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_negative_linear_to_linear_category.
    - intro a; cbn in a.
      use tpair.
      + exact ⇑a.
      + apply weq_submm_iso_z_iso.
        change (⇑a ≅{_l} a).
        exact (force a).
  Defined.

End equivalences.

(** ** Shift functors *)

Section shift_functors.
  Context {D : duploid}.

  (** *** Universal properties of shifts *)

  (** Negative shifts *)
  Definition negative_lift {a b : D} (f : a --> b)
    : a --> ⇑b := f · delay b.

  Definition negative_lift_property {a b : D} (f : a --> b)
    : negative_lift f · force b = f.
  Proof. apply delay_force_right. Qed.

  Definition negative_lift_unique {a b : D} (f : a --> b)
    (f' : a --> ⇑b) (Hf' : f' · force b = f)
    : f' = negative_lift f.
  Proof.
    apply (maponpaths (λ x, negative_lift x)) in Hf'.
    refine (_ @ Hf').
    apply pathsinv0.
    refine (assoc'_negative ⇑b ummsolve _ _ _ @ _).
    apply magmoid_remove_id_right, force_delay_id.
  Qed.

  Corollary negative_lift_univprop {a b : D} (f : a --> b)
    : ∃! (f' : a --> ⇑b), f' · force b = f.
  Proof.
    use unique_exists.
    - exact (negative_lift f).
    - exact (negative_lift_property f).
    - intro; apply unital_magmoid_has_homsets.
    - exact (negative_lift_unique f).
  Defined.

  Corollary isweq_negative_lift (a b : D)
    : isweq (@negative_lift a b).
  Proof.
    exact (weqproperty (invweq (make_weq _ negative_lift_univprop))).
  Defined.

  Lemma negative_lift_linear {a b : D} (f : a --> b)
    (Hf : is_linear f) : is_linear (negative_lift f).
  Proof. apply is_linear_compose; solve [assumption|submagmoid]. Qed.

  (** Positive shifts *)
  Definition positive_lift {a b : D} (f : a <-- b)
    : a <-- ⇓b := f ∘ unwrap b.

  Definition positive_lift_property {a b : D} (f : a <-- b)
    : positive_lift f ∘ wrap b = f.
  Proof. apply wrap_unwrap_left. Qed.

  Definition positive_lift_unique {a b : D} (f : a <-- b)
    (f' : a <-- ⇓b) (Hf' : f' ∘ wrap b = f)
    : f' = positive_lift f.
  Proof.
    apply (maponpaths (λ x, positive_lift x)) in Hf'.
    refine (_ @ Hf').
    apply pathsinv0.
    refine (assoc_positive ⇓b ummsolve _ _ _ @ _).
    apply magmoid_remove_id_left, unwrap_wrap_id.
  Qed.

  Corollary positive_lift_univprop {a b : D} (f : a <-- b)
    : ∃! (f' : a <-- ⇓b), f' ∘ wrap b = f.
  Proof.
    use unique_exists.
    - exact (positive_lift f).
    - exact (positive_lift_property f).
    - intro; apply unital_magmoid_has_homsets.
    - exact (positive_lift_unique f).
  Defined.

  Corollary isweq_positive_lift (a b : D)
    : isweq (@positive_lift a b).
  Proof.
    exact (weqproperty (invweq (make_weq _ positive_lift_univprop))).
  Defined.

  Lemma positive_lift_thunkable {a b : D} (f : a <-- b)
    (Hf : is_thunkable f) : is_thunkable (positive_lift f).
  Proof. apply is_thunkable_compose; solve [assumption|submagmoid]. Qed.

  (** *** Definition of shift functors *)

  Definition upshiftf {a b : D} (f : a --> b) : ⇑a --> ⇑b := negative_lift (force a · f).
  Definition downshiftf {a b : D} (f : a --> b) : ⇓a --> ⇓b := positive_lift (f · wrap b).
  Local Notation "'#⇑'" := upshiftf : duploid.
    (* type in Emacs using agda-input with # \Uparrow *)
  Local Notation "'#⇓'" := downshiftf : duploid.
  (* type in Emacs using agda-input with # \Downarrow *)

  (** Upshift functor *)

  Lemma upshiftf_id (a : D) : #⇑(identity a) = identity ⇑a.
  Proof.
    apply pathsinv0, negative_lift_unique.
    exact (magmoid_id_left _ @ !magmoid_id_right _).
  Qed.

  Lemma upshiftf_comp {a b c : D} (f : a --> b) (g : b --> c)
    (H : is_linear g) : #⇑(f · g) = (#⇑f) · (#⇑g).
  Proof.
    apply pathsinv0, negative_lift_unique.
    rewrite (assoc'_negative ⇑b ummsolve).
    etrans; [apply cancel_precomposition, negative_lift_property|].
    rewrite (assoc_negative ⇑b ummsolve).
    etrans; [apply cancel_postcomposition, negative_lift_property|].
    apply (assoc'_linear _ H).
  Qed.

  Lemma is_linear_upshiftf {a b : D} (f : a --> b) (H : is_linear f)
    : is_linear (#⇑f).
  Proof.
    repeat (apply is_linear_compose);
      solve [assumption|submagmoid].
  Defined.

  Definition upshift_'_to_neg_data : functor_data D (D⁻).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f.
      apply weq_negative_mor.
      exact (upshiftf f).
  Defined.

  Definition upshift_l_to_neg_l_data : functor_data D ₗ (D⁻ₗ).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f; cbn in f.
      apply weq_negative_linear_mor.
      apply (make_submm_mor _l (upshiftf f)).
      apply is_linear_upshiftf; submagmoid.
  Defined.

  Lemma upshift_l_to_neg_l_laws : is_functor upshift_l_to_neg_l_data.
  Proof.
    split.
    - intro a; apply submm_mor_eq.
      apply upshiftf_id.
    - intros a b c f g; apply submm_mor_eq.
      apply upshiftf_comp; submagmoid.
  Qed.

  Definition upshift_l_to_neg_l : functor D ₗ (D⁻ₗ)
    := make_functor _ upshift_l_to_neg_l_laws.

  Definition upshift_pos_t_to_neg_l : functor (D⁺ₜ) (D⁻ₗ)
    := positive_thunkable_to_linear_category D ∙ upshift_l_to_neg_l.

  (** Downshift functor *)

  Lemma downshiftf_id (a : D) : #⇓(identity a) = identity ⇓a.
  Proof.
    apply pathsinv0, positive_lift_unique.
    exact (magmoid_id_right _ @ !magmoid_id_left _).
  Qed.

  Lemma downshiftf_comp {a b c : D} (f : a <-- b) (g : b <-- c)
    (H : is_thunkable g) : #⇓(f ∘ g) = (#⇓f) ∘ (#⇓g).
  Proof.
    apply pathsinv0, positive_lift_unique.
    rewrite (assoc_positive ⇓b ummsolve).
    etrans; [apply cancel_postcomposition, positive_lift_property|].
    rewrite (assoc'_positive ⇓b ummsolve).
    etrans; [apply cancel_precomposition, positive_lift_property|].
    apply (assoc_thunkable _ H).
  Qed.

  Lemma is_thunkable_downshiftf {a b : D} (f : a <-- b) (H : is_thunkable f)
    : is_thunkable (#⇓f).
  Proof.
    repeat (apply is_thunkable_compose);
      solve [assumption|submagmoid].
  Defined.

  Definition downshift_'_to_pos_data : functor_data D (D⁺).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f.
      apply weq_positive_mor.
      exact (downshiftf f).
  Defined.

  Definition downshift_t_to_pos_t_data : functor_data D ₜ (D⁺ₜ).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f; cbn in f.
      apply weq_positive_thunkable_mor.
      apply (make_submm_mor _t (downshiftf f)).
      apply is_thunkable_downshiftf; submagmoid.
  Defined.

  Lemma downshift_t_to_pos_t_laws : is_functor downshift_t_to_pos_t_data.
  Proof.
    split.
    - intro a; apply submm_mor_eq.
      apply downshiftf_id.
    - intros a b c f g; apply submm_mor_eq.
      apply downshiftf_comp; submagmoid.
  Qed.

  Definition downshift_t_to_pos_t : functor D ₜ (D⁺ₜ)
    := make_functor _ downshift_t_to_pos_t_laws.

  Definition downshift_neg_l_to_pos_t : functor (D⁻ₗ) (D⁺ₜ)
    := negative_linear_to_thunkable_category D ∙ downshift_t_to_pos_t.

  (** *** Adjunction [⇑ ⊣ ⇓ : D⁻ₗ ⟶ D⁺ₜ] *)

  (** Naturality of [wrap] *)
  Lemma wrap_natural (a b : D) (f : D⟦a, b⟧)
    : f · wrap b = wrap a · #⇓ f.
  Proof. apply pathsinv0, wrap_unwrap_left. Qed.

  (** Naturality of [unwrap] *)
  Lemma unwrap_natural (a b : D) (f : D⟦a, b⟧)
    : #⇓ f · unwrap b = unwrap a · f.
  Proof.
    apply positive_lift_unique.
    etrans; [apply assoc_thunkable; submagmoid|].
    etrans; [apply cancel_postcomposition, positive_lift_property|].
    apply wrap_unwrap_right.
  Qed.

  (** Naturality of [force] *)
  Lemma force_natural (a b : D) (f : D⟦a, b⟧)
    : #⇑ f · force b = force a · f.
  Proof. apply delay_force_right. Qed.

  (** Naturality of [delay] *)
  Lemma delay_natural (a b : D) (f : D⟦a, b⟧)
    : f · delay b = delay a · #⇑ f.
  Proof.
    apply pathsinv0, negative_lift_unique.
    etrans; [apply assoc'_linear; submagmoid|].
    etrans; [apply cancel_precomposition, negative_lift_property|].
    apply delay_force_left.
  Qed.

  (* We prove the adjunction [⇑ ⊣ ⇓ : D⁻ₗ ⟶ D⁺ₜ] by direct
     computation, since it does not require much extra machinery. *)

  Lemma adjunction_data_neg_l_to_pos_t : adjunction_data D⁺ₜ D⁻ₗ.
  Proof.
    use make_adjunction_data.
    - exact upshift_pos_t_to_neg_l.
    - exact downshift_neg_l_to_pos_t.
    - use make_nat_trans.
      + intro a; cbn in a.
        change (a -->{_lt} ⇓⇑a).
        apply weq_positive_thunkable_mor.
        apply (make_submm_mor _t (delay a · wrap ⇑a)).
        apply is_thunkable_compose;
          solve [apply is_thunkable_delay|submagmoid].
      + intros a b f; apply submm_mor_eq.
        cbn in a, b |- *.
        change (a -->{_lt} b) in f.
        change (f · (delay b · wrap ⇑b) = (delay a · wrap ⇑a) · #⇓(#⇑f)).
        refine (assoc_thunkable f ummsolve _ _ @ _).
        etrans; [apply cancel_postcomposition, delay_natural|].
        refine (assoc'_thunkable (delay a) ummsolve _ _ @ _).
        refine (_ @ assoc_thunkable (delay a) ummsolve _ _).
        apply cancel_precomposition.
        apply wrap_natural.
    - use make_nat_trans.
      + intro a; cbn in a.
        change (a <--{_lt} ⇑⇓a).
        apply weq_negative_linear_mor.
        apply (make_submm_mor _l (unwrap a ∘ force ⇓a)).
        apply is_linear_compose;
          solve [apply is_linear_unwrap|submagmoid].
      + intros a b f; apply submm_mor_eq.
        cbn in a, b |- *.
        change (a -->{_lt} b) in f.
        change ((unwrap b ∘ force ⇓b) ∘ #⇑(#⇓f) = f ∘ (unwrap a ∘ force ⇓a)).
        apply pathsinv0.
        refine (assoc'_linear f ummsolve _ _ @ _).
        etrans; [apply cancel_precomposition, pathsinv0, unwrap_natural|].
        refine (assoc_linear (unwrap b) ummsolve _ _ @ _).
        refine (_ @ assoc'_linear (unwrap b) ummsolve _ _).
        apply cancel_postcomposition.
        apply pathsinv0, force_natural.
  Defined.

  Lemma form_adjunction_neg_l_to_pos_t
    : form_adjunction' adjunction_data_neg_l_to_pos_t.
  Proof.
    split.
    - intros a; apply submm_mor_eq; cbn in a.
      change (#⇑(delay a · wrap ⇑a) · (force ⇓⇑a · unwrap ⇑a) = identity ⇑a).
      rewrite (assoc_negative ⇑⇓⇑a ummsolve).
      rewrite force_natural, wrap_natural.
      rewrite (assoc_positive ⇓a ummsolve).
      rewrite (assoc'_positive ⇓⇑a ummsolve).
      rewrite unwrap_natural.
      rewrite wrap_unwrap_interpose.
      apply force_delay_id.
    - intros a; apply submm_mor_eq; cbn in a.
      change (#⇓(unwrap a ∘ force ⇓a) ∘ (wrap ⇑⇓a ∘ delay ⇓a) = identity ⇓a).
      rewrite (assoc'_positive ⇓⇑⇓a ummsolve).
      rewrite <- wrap_natural, <- force_natural.
      rewrite (assoc'_negative ⇑a ummsolve).
      rewrite (assoc_negative ⇑⇓a ummsolve).
      rewrite <- delay_natural.
      rewrite delay_force_interpose.
      apply unwrap_wrap_id.
  Qed.

  Definition adjunction_neg_l_to_pos_t : adjunction D⁺ₜ D⁻ₗ.
  Proof.
    use make_adjunction.
    - exact adjunction_data_neg_l_to_pos_t.
    - exact form_adjunction_neg_l_to_pos_t.
  Defined.

End shift_functors.
Notation "'#⇑'" := upshiftf : duploid.
  (* type in Emacs using agda-input with # \Uparrow *)
Notation "'#⇓'" := downshiftf : duploid.
  (* type in Emacs using agda-input with # \Downarrow *)
