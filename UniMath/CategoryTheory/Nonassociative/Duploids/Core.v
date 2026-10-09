(********************************************************************************

 [Pre]duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Polarity shifts
 2. Polarization property
 3. Definition of a preduploid
 4. Definition of a duploid
 5. Lemmas about shifts

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.

Local Open Scope cat.
Local Open Scope unital_magmoid.

Declare Scope duploid.
Delimit Scope duploid with duploid.
Local Open Scope duploid.

(** ** Polarization property/structure *)

Section polarities.

  (** *** Polarization property *)

  (** Property to say that a is negative, positive, or both. *)
  Definition has_polarity {M : unital_premagmoid} (a : M) : UU
    := ∥ is_negative a ⨿ is_positive a ∥.
  Definition make_has_polarity_negative {M : unital_premagmoid} (a : M)
    (H : is_negative a) : has_polarity a := hinhpr (ii1 H).
  Definition make_has_polarity_positive {M : unital_premagmoid} (a : M)
    (H : is_positive a) : has_polarity a := hinhpr (ii2 H).

  Lemma isaprop_has_polarity {M : unital_premagmoid} (a : M) : isaprop (has_polarity a).
  Proof. apply isapropishinh. Qed.

  Definition has_polarities (M : unital_premagmoid) : UU
    := ∏ (a : M), has_polarity a.
  Definition polarity_of {M : unital_premagmoid} (H : has_polarities M) (a : M)
    : has_polarity a := H a.

  Lemma isaprop_has_polarities (M : unital_premagmoid) : isaprop (has_polarities M).
  Proof. apply impred; intro a; apply isaprop_has_polarity. Qed.

  (** Non-dependent induction scheme for polarities. *)
  Lemma has_polarity_rec {M : unital_premagmoid}
    {a : M} (H : has_polarity a)
    {P : UU} (HP : isaprop P)
    (H1 : ∏ (negp : is_negative a), P)
    (H2 : ∏ (posp : is_positive a), P)
    : P.
  Proof.
    refine (factor_through_squash HP _ H).
    intro H'; induction H'.
    - now apply H1.
    - now apply H2.
  Defined.

  (** Dependent induction scheme for polarities. *)
  Lemma has_polarity_rec_dep {M : unital_premagmoid}
    {a : M} (H : has_polarity a)
    {P : has_polarity a -> UU}
    (HP : isPredicate P)
    (H1 : ∏ (negp : is_negative a), P (hinhpr (ii1 negp)))
    (H2 : ∏ (posp : is_positive a), P (hinhpr (ii2 posp)))
    : P H.
  Proof.
    apply (squash_rec (λ a, make_hProp (P a) (HP a))).
    intro H'; induction H'.
    - now apply H1.
    - now apply H2.
  Defined.

  (** Preduploid definition *)
  Definition preduploid : UU
    := ∑ (M : unital_magmoid), has_polarities M.
  Coercion preduploid_to_unital_magmoid (D : preduploid) : unital_magmoid := pr1 D.
  Coercion preduploid_has_polarities (D : preduploid) : has_polarities D := pr2 D.

  Definition make_preduploid
    (M : unital_magmoid)
    (H : has_polarities M)
    : preduploid
    := M,, H.

  (** *** Polarization structure *)

  Definition hpolarity : hSet := make_hSet bool isasetbool.
  Definition chpositive : hpolarity := true.
  Definition chnegative : hpolarity := false.
  Local Notation "'⊕'" := chpositive : duploid.
  Local Notation "'⊖'" := chnegative : duploid.

  Definition is_polarity_mapping
    {D : unital_premagmoid_data} (ω : D -> hpolarity) : UU
    := ∏ (a : D), if ω a then is_positive a else is_negative a.

  Lemma isaprop_is_polarity_mapping
    {D : unital_magmoid} (ω : D -> hpolarity)
    : isaprop (is_polarity_mapping ω).
  Proof.
    apply impred; intro a.
    induction (ω a).
    - apply isaprop_is_positive.
    - apply isaprop_is_negative.
  Qed.

  Definition polarity_mapping (D : unital_premagmoid_data) : UU
    := ∑ (ω : D -> hpolarity), is_polarity_mapping ω.
  Definition polarity_mapping_to_mapping {D : unital_premagmoid_data}
    (ω : polarity_mapping D) : D -> hpolarity
    := pr1 ω.
  Coercion polarity_mapping_to_mapping : polarity_mapping >-> Funclass.
  Definition polarity_mapping_property {D : unital_premagmoid_data}
    (ω : polarity_mapping D) : is_polarity_mapping ω
    := pr2 ω.

  Definition make_polarity_mapping {D : unital_premagmoid_data}
    (ω : D -> hpolarity) (Hω : is_polarity_mapping ω)
    : polarity_mapping D
    := ω,, Hω.

  Lemma pmap_positive' {D : unital_premagmoid_data}
    (ω : polarity_mapping D) (a : D) : ω a = ⊕ -> is_positive a.
  Proof.
    intro Ha.
    exact (transportf (λ (x : hpolarity), if x then _ else _) Ha
             (polarity_mapping_property ω a)).
  Defined.
  Lemma pmap_negative' {D : unital_premagmoid_data}
    (ω : polarity_mapping D) (a : D) : ω a = ⊖ -> is_negative a.
  Proof.
    intro Ha.
    exact (transportf (λ (x : hpolarity), if x then _ else _) Ha
             (polarity_mapping_property ω a)).
  Defined.

  Definition polarity_mapping_alt (D : unital_premagmoid_data) : UU
    := ∏ (a : D), is_negative a ⨿ is_positive a.

  Definition make_polarity_mapping' {D : unital_premagmoid_data}
    (ω : polarity_mapping_alt D) : polarity_mapping D.
  Proof.
    use make_polarity_mapping.
    - intro a.
      induction (ω a).
      + exact ⊖.
      + exact ⊕.
    - intro a.
      now induction (ω a).
  Defined.

  Lemma decide_polarity {D : unital_premagmoid_data}
    (ω : polarity_mapping D) : polarity_mapping_alt D.
  Proof.
    intro a.
    induction (_,,idpath _ : paths_from (ω a)) as [ωa Hωa].
    induction ωa.
    - right; apply (pmap_positive' ω a Hωa).
    - left; apply (pmap_negative' ω a Hωa).
  Defined.

  Definition ish_chpositive'
    {M : unital_magmoid} (ω : M -> hpolarity)
    : hsubtype M
    := λ a, make_hProp (ω a = ⊕) (setproperty hpolarity _ _).

  Definition ish_chnegative'
    {M : unital_magmoid} (ω : M -> hpolarity)
    : hsubtype M
    := λ a, make_hProp (ω a = ⊖) (setproperty hpolarity _ _).

  (** Split preduploid definition *)
  Definition split_preduploid : UU
    := ∑ (D : preduploid), polarity_mapping D.
  Coercion split_preduploid_to_preduploid
    (D : split_preduploid) : preduploid := pr1 D.
  Coercion polarity_mapping_of
    (D : split_preduploid) : polarity_mapping D := pr2 D.

  Definition make_split_preduploid'
    (D : preduploid)
    (ω : polarity_mapping D)
    : split_preduploid
    := D,, ω.

  Definition make_split_preduploid
    (D : unital_magmoid)
    (ω : polarity_mapping D)
    : split_preduploid.
  Proof.
    use make_split_preduploid'.
    - use make_preduploid.
      + exact D.
      + intro a; apply hinhpr.
        exact (decide_polarity ω a).
    - exact ω.
  Defined.

  Definition ish_chpositive {D : split_preduploid}
    : hsubtype D := ish_chpositive' D.
  Definition ish_chnegative {D : split_preduploid}
    : hsubtype D := ish_chnegative' D.

  Lemma pmap_positive {D : split_preduploid} (a : D)
    : polarity_mapping_of D a = ⊕ -> is_positive a.
  Proof. apply pmap_positive'. Qed.
  Lemma pmap_negative {D : split_preduploid} (a : D)
    : polarity_mapping_of D a = ⊖ -> is_negative a.
  Proof. apply pmap_negative'. Qed.

End polarities.
Notation "'^⊕ω'" := ish_chpositive : unital_magmoid.
Notation "'^⊖ω'" := ish_chnegative : unital_magmoid.

(** ** Polarity shifts *)

Section shifts.

  (** Upshifts, or negative shifts. *)
  Definition negative_shift_data (M : unital_magmoid) : UU :=
    ∏ a : M, ∑ upshift : M, upshift --> a.
  Definition make_negative_shift_data {M : unital_magmoid}
    (upshift : M -> M) (force : ∏ (a : M), upshift a --> a)
    : negative_shift_data M :=
    λ a, upshift a,,force a.
  Definition upshift' {M : unital_magmoid} (D : negative_shift_data M) : M -> M := λ a, pr1 (D a).
  Definition force' {M : unital_magmoid} (D : negative_shift_data M) (a : M) : upshift' D a --> a := pr2 (D a).

  Definition negative_shift_axioms {M : unital_magmoid} (D : negative_shift_data M) : UU
    := (∏ (a : M), is_linear (force' D a)) ×
         (∏ (a : M), is_negative (upshift' D a)) ×
         (∏ (a : M), has_linear_inverse (force' D a)).

  Definition make_negative_shift_axioms {M : unital_magmoid} {D : negative_shift_data M}
    (H1 : ∏ a : M, is_linear (force' D a))
    (H2 : ∏ a : M, is_negative (upshift' D a))
    (H3 : ∏ a : M, has_linear_inverse (force' D a))
    : negative_shift_axioms D
    := H1,,H2,,H3.

  Definition is_linear_force' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : is_linear (force' D a) := pr1 H a.
  Definition is_negative_upshift' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : is_negative (upshift' D a) := pr12 H a.
  Definition has_linear_inverse_force' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : has_linear_inverse (force' D a) := pr22 H a.
  Definition delay' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : a -->{_l} upshift' D a
    := submm_inv_mor _l (has_linear_inverse_force' H a).

  Lemma isaprop_negative_shift_axioms {M : unital_magmoid} (D : negative_shift_data M)
    : isaprop (negative_shift_axioms D).
  Proof.
    refine (isapropdirprod _ _ _ (isapropdirprod _ _ _ _));
      apply impred; intro a.
    - apply isaprop_is_linear.
    - apply isaprop_is_negative.
    - apply isaprop_has_linear_inverse.
  Qed.

  Definition has_negative_shifts (M : unital_magmoid) : UU
    := ∑ (D : negative_shift_data M), negative_shift_axioms D.
  Definition make_has_negative_shifts {M : unital_magmoid}
    (D : negative_shift_data M) (H : negative_shift_axioms D)
    : has_negative_shifts M := D,,H.
  Coercion has_negative_shifts_to_negative_shift_data (M : unital_magmoid)
    (H : has_negative_shifts M) : negative_shift_data M := pr1 H.
  Coercion has_negative_shifts_to_negative_shift_axioms (M : unital_magmoid)
    (H : has_negative_shifts M) : negative_shift_axioms H := pr2 H.

  (** Downshifts, or positive shifts. *)
  Definition positive_shift_data (M : unital_magmoid) : UU :=
    ∏ a : M, ∑ downshift : M, downshift <-- a.
  Definition make_positive_shift_data {M : unital_magmoid}
    (downshift : M -> M) (wrap : ∏ (a : M), downshift a <-- a)
    : positive_shift_data M :=
    λ a, downshift a,,wrap a.
  Definition downshift' {M : unital_magmoid} (D : positive_shift_data M) : M -> M := λ a, pr1 (D a).
  Definition wrap' {M : unital_magmoid} (D : positive_shift_data M) (a : M) : downshift' D a <-- a := pr2 (D a).

  Definition positive_shift_axioms {M : unital_magmoid} (D : positive_shift_data M) : UU
    := (∏ (a : M), is_thunkable (wrap' D a)) ×
         (∏ (a : M), is_positive (downshift' D a)) ×
         (∏ (a : M), has_thunkable_inverse (wrap' D a)).

  Definition make_positive_shift_axioms {M : unital_magmoid} {D : positive_shift_data M}
    (H1 : ∏ a : M, is_thunkable (wrap' D a))
    (H2 : ∏ a : M, is_positive (downshift' D a))
    (H3 : ∏ a : M, has_thunkable_inverse (wrap' D a))
    : positive_shift_axioms D
    := H1,,H2,,H3.

  Definition is_thunkable_wrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : is_thunkable (wrap' D a) := pr1 H a.
  Definition is_positive_downshift' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : is_positive (downshift' D a) := pr12 H a.
  Definition has_thunkable_inverse_wrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : has_thunkable_inverse (wrap' D a) := pr22 H a.
  Definition unwrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : downshift' D a -->{_t} a
    := submm_inv_mor _t (has_thunkable_inverse_wrap' H a).

  Lemma isaprop_positive_shift_axioms {M : unital_magmoid} (D : positive_shift_data M)
    : isaprop (positive_shift_axioms D).
  Proof.
    refine (isapropdirprod _ _ _ (isapropdirprod _ _ _ _));
      apply impred; intro a.
    - apply isaprop_is_thunkable.
    - apply isaprop_is_positive.
    - apply isaprop_has_thunkable_inverse.
  Qed.

  Definition has_positive_shifts (M : unital_magmoid) : UU
    := ∑ (D : positive_shift_data M), positive_shift_axioms D.
  Definition make_has_positive_shifts {M : unital_magmoid}
    (D : positive_shift_data M) (H : positive_shift_axioms D)
    : has_positive_shifts M := D,,H.
  Coercion has_positive_shifts_to_positive_shift_data (M : unital_magmoid)
    (H : has_positive_shifts M) : positive_shift_data M := pr1 H.
  Coercion has_positive_shifts_to_positive_shift_axioms (M : unital_magmoid)
    (H : has_positive_shifts M) : positive_shift_axioms H := pr2 H.

  (** Combined shifts *)
  Definition has_polarity_shifts (M : unital_magmoid) : UU
    := has_negative_shifts M × has_positive_shifts M.
  Definition make_has_polarity_shifts {M : unital_magmoid}
    (H1 : has_negative_shifts M)
    (H2 : has_positive_shifts M)
    : has_polarity_shifts M := H1,,H2.
  Coercion has_polarity_shifts_to_has_negative_shifts {M : unital_magmoid}
    (H : has_polarity_shifts M) : has_negative_shifts M := pr1 H.
  Coercion has_polarity_shifts_to_has_positive_shifts {M : unital_magmoid}
    (H : has_polarity_shifts M) : has_positive_shifts M := pr2 H.

  (** Definition of duploid *)
  Definition duploid : UU
    := ∑ (D : preduploid), has_polarity_shifts D.
  Coercion duploid_to_preduploid (D : duploid) : preduploid := pr1 D.
  Coercion duploid_has_polarity_shifts (D : duploid) : has_polarity_shifts D := pr2 D.

  Definition make_duploid
    (D : preduploid)
    (S : has_polarity_shifts D)
    : duploid
    := D,, S.

  (** Upshifts *)
  Definition upshift {D : duploid} (a : D) : sub_ob D ^⊖
    := make_sub_ob ^⊖ (upshift' D a) (is_negative_upshift' D a).
  Notation "'⇑' a" := (upshift a) (at level 5, right associativity, format "⇑ a") : duploid.
    (* type in Emacs using agda-input with \Uparrow *)

  Definition force {D : duploid} (a : D) : ⇑a ≅{_l} a.
  Proof.
    use make_submm_iso.
    - exact (force' D a).
    - use make_is_submm_iso.
      + exact (is_linear_force' D a).
      + exact (has_linear_inverse_force' D a).
  Defined.
  Definition delay {D : duploid} (a : D) : a ≅{_l} ⇑a
    := submm_iso_inv _ (force a).

  (** Downshifts *)
  Definition downshift {D : duploid} (a : D) : sub_ob D ^⊕
    := make_sub_ob ^⊕ (downshift' D a) (is_positive_downshift' D a).
  Notation "'⇓' a" := (downshift a) (at level 5, right associativity, format "⇓ a") : duploid.
    (* type in Emacs using agda-input with \Downarrow *)

  Definition wrap {D : duploid} (a : D) : a ≅{_t} ⇓a.
  Proof.
    use make_submm_iso.
    - exact (wrap' D a).
    - use make_is_submm_iso.
      + exact (is_thunkable_wrap' D a).
      + exact (has_thunkable_inverse_wrap' D a).
  Defined.
  Definition unwrap {D : duploid} (a : D) : ⇓a ≅{_t} a
    := submm_iso_inv _ (wrap a).

  (** *** Mapping-respecting shifts *)
  Definition pmap_respects_negative_shifts
    {M : unital_magmoid}
    (S : negative_shift_data M)
    (ω : M -> hpolarity) : UU
    := ∏ (a : M), ω (upshift' S a) = chnegative.

  Lemma isaprop_pmap_respects_negative_shifts
    {M : unital_magmoid}
    (S : negative_shift_data M)
    (ω : M -> hpolarity)
    : isaprop (pmap_respects_negative_shifts S ω).
  Proof.
    apply impred; intro.
    apply setproperty.
  Qed.

  Definition has_split_negative_shifts
    (M : unital_magmoid) (ω : M -> hpolarity) : UU
    := ∑ (S : has_negative_shifts M),
      pmap_respects_negative_shifts S ω.

  Definition pmap_respects_positive_shifts
    {M : unital_magmoid}
    (S : positive_shift_data M)
    (ω : M -> hpolarity) : UU
    := ∏ (a : M), ω (downshift' S a) = chpositive.

  Lemma isaprop_pmap_respects_positive_shifts
    {M : unital_magmoid}
    (S : positive_shift_data M)
    (ω : M -> hpolarity)
    : isaprop (pmap_respects_positive_shifts S ω).
  Proof.
    apply impred; intro.
    apply setproperty.
  Qed.

  Definition has_split_positive_shifts
    (M : unital_magmoid) (ω : M -> hpolarity) : UU
    := ∑ (S : has_positive_shifts M),
      pmap_respects_positive_shifts S ω.

  Definition pmap_respects_shifts
    {M : unital_magmoid}
    (S : has_polarity_shifts M)
    (ω : M -> hpolarity) : UU
    := pmap_respects_negative_shifts S ω
         × pmap_respects_positive_shifts S ω.

  Lemma isaprop_pmap_respects_shifts
    {M : unital_magmoid}
    (S : has_polarity_shifts M)
    (ω : M -> hpolarity)
    : isaprop (pmap_respects_shifts S ω).
  Proof.
    apply isapropdirprod.
    - apply isaprop_pmap_respects_negative_shifts.
    - apply isaprop_pmap_respects_positive_shifts.
  Qed.

  (** Split duploid *)
  Definition split_duploid : UU
    := ∑ (D : duploid) (ω : polarity_mapping D),
      pmap_respects_shifts D ω.

  Definition make_split_duploid'
    (D : duploid)
    (ω : polarity_mapping D)
    (H : pmap_respects_shifts D ω)
    : split_duploid
    := D,, ω,, H.

  Definition make_split_duploid
    (D : split_preduploid)
    (S : has_polarity_shifts D)
    (H : pmap_respects_shifts S D)
    : split_duploid.
  Proof.
    use make_split_duploid'.
    - use make_duploid.
      + exact D.
      + exact S.
    - exact D.
    - exact H.
  Defined.

  (** We are careful with the coercions so that unification can find
      both [D : duploid] and [D : split_preduploid] as the implicit
      argument from an [a : D].  We effectively witness the "diamond
      problem" of multiple inheritance here. *)
  Definition split_duploid_to_duploid (D : split_duploid) : duploid := pr1 D.
  Coercion split_duploid_to_split_preduploid (D : split_duploid) : split_preduploid
    := make_split_preduploid' (split_duploid_to_duploid D) (pr12 D).
  Coercion split_duploid_to_duploid : split_duploid >-> duploid.

  (** Checking the coercions... *)
  Section check.
    (* Local Set Printing Coercions. Local Set Printing Implicit. *)
    Check λ (D : split_duploid), sub_ob D ^⊕ω.
    Check λ (D : split_duploid) (a : D), delay a.
  End check.

  Definition split_duploid_pmap_respects_shifts (D : split_duploid)
    : pmap_respects_shifts D D := pr22 D.

  (* Example: unification would not be able to find that [⇑a] belongs
     to a split preduploid.  So, [polarity_mapping_of _ ⇑a]
     fails to typecheck, but [polarity_mapping_of _ a] succeeds. *)
  Lemma pmap_upshift {D : split_duploid} (a : D)
    : polarity_mapping_of D ⇑a = chnegative.
  Proof. apply split_duploid_pmap_respects_shifts. Defined.
  Lemma pmap_downshift {D : split_duploid} (a : D)
    : polarity_mapping_of D ⇓a = chpositive.
  Proof. apply split_duploid_pmap_respects_shifts. Defined.

  Definition chnegative_upshift {D : split_duploid} (a : D)
    : sub_ob D ^⊖ω.
  Proof.
    use make_sub_ob.
    - exact ⇑a.
    - apply pmap_upshift.
  Defined.
  Definition chpositive_downshift {D : split_duploid} (a : D)
    : sub_ob D ^⊕ω.
  Proof.
    use make_sub_ob.
    - exact ⇓a.
    - apply pmap_downshift.
  Defined.

End shifts.
Notation "'⇑' a" := (upshift a) (at level 5, right associativity, format "⇑ a") : duploid.
  (* type in Emacs using agda-input with \Uparrow *)
Notation "'⇓' a" := (downshift a) (at level 5, right associativity, format "⇓ a") : duploid.
  (* type in Emacs using agda-input with \Downarrow *)

(** ** Lemmas about shifts *)

Section shift_lemmas.
  Context {D : duploid}.

  (* [force] and [delay] lemmas. *)
  Lemma force_delay_id (a : D) : force a · delay a = identity ⇑a.
  Proof. apply (is_inverse_in_precat1 (force a)). Defined.
  Lemma delay_force_id (a : D) : delay a · force a = identity a.
  Proof. apply (is_inverse_in_precat2 (force a)). Defined.
  Lemma delay_force_right {a b : D} (f : a --> b) : (f · delay b) · force b = f.
  Proof. apply submm_iso_right_of_linear; submagmoid. Defined.
  Lemma delay_force_left {a b : D} (f : a --> b) : delay a · (force a · f) = f.
  Proof. apply submm_iso_left_of_thunkable; submagmoid. Defined.
  Lemma delay_force_interpose {a b c : D} (f : a --> b) (g : b --> c)
    : (f · delay b) · (force b · g) = f · g.
  Proof. now rewrite (assoc_negative ⇑b ummsolve), delay_force_right. Qed.

  (* [wrap] and [unwrap] lemmas. *)
  Lemma unwrap_wrap_id (a : D) : unwrap a · wrap a = identity ⇓a.
  Proof. apply (is_inverse_in_precat2 (wrap a)). Defined.
  Lemma wrap_unwrap_id (a : D) : wrap a · unwrap a = identity a.
  Proof. apply (is_inverse_in_precat1 (wrap a)). Defined.
  Lemma wrap_unwrap_right {a b : D} (f : a <-- b) : (f · wrap a) · unwrap a = f.
  Proof. apply submm_iso_right_of_inv_linear; submagmoid. Defined.
  Lemma wrap_unwrap_left {a b : D} (f : a <-- b) : wrap b · (unwrap b · f) = f.
  Proof. apply submm_iso_left_of_thunkable; submagmoid. Defined.
  Lemma wrap_unwrap_interpose {a b c : D} (f : a --> b) (g : b --> c)
    : (f · wrap b) · (unwrap b · g) = f · g.
  Proof. now rewrite (assoc'_positive ⇓b ummsolve), wrap_unwrap_left. Qed.

  (** Force and wrap are intermediate. *)

  Lemma is_intermediate_force (a : D) : is_intermediate (force a).
  Proof. apply is_intermediate_of_negative; submagmoid. Qed.
  Lemma is_intermediate_wrap (a : D) : is_intermediate (wrap a).
  Proof. apply is_intermediate_of_positive; submagmoid. Qed.

  (** Characterisation of thunkable and linear morphisms *)

  Lemma is_thunkable_of_delay_wrap {a b : D} (f : a --> b)
    : f · (delay b · wrap ⇑b) = (f · delay b) · wrap ⇑b ->
      is_thunkable f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : D) (h : ⇑b --> d), f · (delay b · h) = (f · delay b) · h). {
      intros d h.
      rewrite <- (wrap_unwrap_interpose (delay b) h).
      rewrite (assoc_positive ⇓⇑b ummsolve), Hf.
      rewrite (assoc'_negative ⇑b ummsolve).
      now rewrite wrap_unwrap_left.
    }
    intros c d g h.
    intermediate_path (f · (delay b · (force b · g) · h)).
    1: now rewrite delay_force_left.
    rewrite (assoc'_negative ⇑b ummsolve), H'.
    rewrite (assoc_negative ⇑b ummsolve), <- H'.
    now rewrite delay_force_left.
  Qed.

  Lemma is_thunkable_iff_delay_wrap {a b : D} (f : a --> b)
    : f · (delay b · wrap ⇑b) = (f · delay b) · wrap ⇑b ≃
        is_thunkable f.
  Proof.
    apply weqimplimpl.
    - apply is_thunkable_of_delay_wrap.
    - intro H; apply assoc_thunkable, H.
    - apply unital_magmoid_has_homsets.
    - apply isaprop_is_thunkable.
  Qed.

  Lemma is_linear_of_force_unwrap {a b : D} (f : b --> a)
    : (force ⇓b · unwrap b) · f = force ⇓b · (unwrap b · f) ->
      is_linear f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : D) (h : d --> ⇓b), (h · unwrap b) · f = h · (unwrap b · f)). {
      intros d h.
      rewrite <- (delay_force_interpose h (unwrap b)).
      rewrite (assoc'_negative ⇑⇓b ummsolve), Hf.
      rewrite (assoc_positive ⇓b ummsolve).
      now rewrite delay_force_right.
    }
    intros c d g h.
    intermediate_path ((h · ((g · wrap b) · unwrap b)) · f).
    1: now rewrite wrap_unwrap_right.
    rewrite (assoc_positive (⇓b) ummsolve), H'.
    rewrite (assoc'_positive (⇓b) ummsolve), <- H'.
    now rewrite wrap_unwrap_right.
  Qed.

  Lemma is_linear_iff_force_unwrap {a b : D} (f : a <-- b)
    : (force ⇓b · unwrap b) · f = force ⇓b · (unwrap b · f) ≃
        is_linear f.
  Proof.
    apply weqimplimpl.
    - apply is_linear_of_force_unwrap.
    - intro H; apply assoc'_linear, H.
    - apply unital_magmoid_has_homsets.
    - apply isaprop_is_linear.
  Qed.

  (** Characterisation of positive and negative objects *)

  (** For an object [a], the following statements are equivalent:
  1. [a] is positive
  2. [wrap a] is linear
  3. [wrap a] is a linear-and-thunkable isomorphism *)

  Lemma is_linear_unwrap (a : D) : is_linear (unwrap a).
  Proof. apply is_linear_of_positive; submagmoid. Qed.
  (** 1 -> 2 *)
  Lemma is_linear_wrap_of_positive (a : D) (H : is_positive a) : is_linear (wrap a).
  Proof. now apply is_linear_of_positive. Qed.

  (** 2 -> 3 *)
  Lemma is_lt_iso_wrap_of_linear (a : D) (H : is_linear (wrap a)) : is_lt_iso (wrap a).
  Proof.
    use make_is_submm_iso'.
    - exact (unwrap a).
    - abstract (split; solve [exact H|submagmoid]).
    - abstract (split; solve [apply is_linear_unwrap|submagmoid]).
    - abstract (exact (wrap a)).
  Defined.

  (** 1 -> 3 *)
  Lemma is_lt_iso_wrap_of_positive (a : D) (H : is_positive a) : is_lt_iso (wrap a).
  Proof.
    apply is_lt_iso_wrap_of_linear.
    abstract (apply is_linear_of_positive, H).
  Defined.

  (** 2 -> 1 (via 3) *)
  Lemma is_positive_of_linear_wrap (a : D) (H : is_linear (wrap a)) : is_positive a.
  Proof.
    refine (is_positive_of_lt_iso (_ : ⇓a ≅{_lt} a) ummsolve).
    eapply submm_iso_inv, make_submm_iso, is_lt_iso_wrap_of_linear, H.
  Qed.

  Lemma is_positive_iff_linear_wrap (a : D) : is_linear (wrap a) ≃ is_positive a.
  Proof.
    apply weqimplimpl.
    - apply is_positive_of_linear_wrap.
    - apply is_linear_wrap_of_positive.
    - apply isaprop_is_linear.
    - apply isaprop_is_positive.
  Qed.

  (** 3 *)
  Lemma lt_iso_downshift_of_positive (a : D) (H : is_positive a) : lt_iso a ⇓a.
  Proof.
    exact (make_submm_iso _lt _ (is_lt_iso_wrap_of_positive a H)).
  Defined.

  Lemma is_lt_iso_unwrap_of_positive (a : D) (H : is_positive a) : is_lt_iso (unwrap a).
  Proof.
    exact (pr2 (submm_iso_inv _lt (lt_iso_downshift_of_positive a H))).
  Defined.

  Lemma is_lt_iso_unwrap_of_linear (a : D) (H : is_linear (wrap a)) : is_lt_iso (unwrap a).
  Proof.
    apply is_lt_iso_unwrap_of_positive, is_positive_of_linear_wrap, H.
  Defined.

  (** For an object [a], the following statements are equivalent:
  1. [a] is negative
  2. [force a] is thunkable
  3. [force a] is a thunkable-and-linear isomorphism *)

  Lemma is_thunkable_delay (a : D) : is_thunkable (delay a).
  Proof. apply is_thunkable_of_negative; submagmoid. Qed.
  (** 1 -> 2 *)
  Lemma is_thunkable_force_of_negative (a : D) (H : is_negative a) : is_thunkable (force a).
  Proof. now apply is_thunkable_of_negative. Qed.

  (** 2 -> 3 *)
  Lemma is_lt_iso_force_of_thunkable (a : D) (H : is_thunkable (force a)) : is_lt_iso (force a).
  Proof.
    use make_is_submm_iso'.
    - exact (delay a).
    - abstract (split; solve [exact H|submagmoid]).
    - abstract (split; solve [apply is_thunkable_delay|submagmoid]).
    - abstract (exact (force a)).
  Defined.

  (** 1 -> 3 *)
  Lemma is_lt_iso_force_of_negative (a : D) (H : is_negative a) : is_lt_iso (force a).
  Proof.
    apply is_lt_iso_force_of_thunkable.
    abstract (apply is_thunkable_of_negative, H).
  Defined.

  (** 2 -> 1 (via 3) *)
  Lemma is_negative_of_thunkable_force (a : D) (H : is_thunkable (force a)) : is_negative a.
  Proof.
    refine (is_negative_of_lt_iso (_ : ⇑a ≅{_lt} a) ummsolve).
    eapply make_submm_iso, is_lt_iso_force_of_thunkable, H.
  Qed.

  Lemma is_negative_iff_thunkable_force (a : D) : is_thunkable (force a) ≃ is_negative a.
  Proof.
    apply weqimplimpl.
    - apply is_negative_of_thunkable_force.
    - apply is_thunkable_force_of_negative.
    - apply isaprop_is_thunkable.
    - apply isaprop_is_negative.
  Qed.

  (** 3 *)
  Lemma lt_iso_upshift_of_negative (a : D) (H : is_negative a) : lt_iso ⇑a a.
  Proof.
    exact (make_submm_iso _lt _ (is_lt_iso_force_of_negative a H)).
  Defined.

  Lemma is_lt_iso_delay_of_negative (a : D) (H : is_negative a) : is_lt_iso (delay a).
  Proof.
    exact (pr2 (submm_iso_inv _lt (lt_iso_upshift_of_negative a H))).
  Defined.

  Lemma is_lt_iso_delay_of_thunkable (a : D) (H : is_thunkable (force a)) : is_lt_iso (delay a).
  Proof.
    apply is_lt_iso_delay_of_negative, is_negative_of_thunkable_force, H.
  Defined.

End shift_lemmas.
