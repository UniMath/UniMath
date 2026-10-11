(********************************************************************************

 The (Two-Sorted) Duploid arising from an Adjunction

 Author: B. Szilvasy
 January–October 2026

 This file defines the oblique duploid in terms of the envelope duploid.

 Contents:
 1. Definition of the oblique duploid
 1.1. Objects and morphisms
 1.2. Polarities and shifts
 1.3. Equivalence between oblique and envelope duploid
 2. Lemmas about the oblique duploid
 2.1. Characterization of polarities
 2.2. Inclusion functors

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.Envelope.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

Section oblique_dupl.
  (** ** Definition of the oblique duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.
  Notation Env := (envelope_duploid θ).

  (** *** Objects and morphisms *)

  Definition oblique_ob : UU := N ⨿ P.
  Definition oblique_to_envelope_ob (a : oblique_ob) : envelope_ob θ.
  Proof.
    induction a as [n | p].
    - exact (envelope_ob_of_negative θ n).
    - exact (envelope_ob_of_positive θ p).
  Defined.
  Local Notation O2E := oblique_to_envelope_ob.

  Definition oblique_ob_of_negative (n : N) : oblique_ob := ii1 n.
  Definition oblique_ob_of_positive (p : P) : oblique_ob := ii2 p.

  Definition oblique_unital_premagmoid_data : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact oblique_ob.
      + intros a b; exact (O2E a --> O2E b).
    - intro a; exact (identity (O2E a)).
    - intros a b c f g.
      cbn -[envelope_duploid] in f, g.
      exact (f · g).
  Defined.

  Definition oblique_is_unital_premagmoid
    : is_unital_premagmoid oblique_unital_premagmoid_data.
  Proof.
    split; intros a b f; cbn -[envelope_duploid].
    - apply magmoid_id_left.
    - apply magmoid_id_right.
  Qed.

  Definition oblique_unital_magmoid : unital_magmoid.
  Proof.
    use make_unital_magmoid.
    - use make_unital_premagmoid.
      + exact oblique_unital_premagmoid_data.
      + exact oblique_is_unital_premagmoid.
    - intros a b.
      apply (unital_magmoid_has_homsets Env).
  Defined.

  Lemma oblique_is_linear_of_envelope {a b : oblique_ob}
    (f : oblique_unital_magmoid⟦a, b⟧)
    (H : is_linear (f : Env⟦O2E a, O2E b⟧))
    : is_linear f.
  Proof.
    intros c d g h; cbn in c, d.
    exact (H _ _ g h).
  Qed.

  Lemma oblique_is_thunkable_of_envelope {a b : oblique_ob}
    (f : oblique_unital_magmoid⟦a, b⟧)
    (H : is_thunkable (f : Env⟦O2E a, O2E b⟧))
    : is_thunkable f.
  Proof.
    intros c d g h; cbn in c, d.
    exact (H _ _ g h).
  Qed.

  Lemma oblique_is_negative_of_envelope (a : oblique_ob)
    (H : is_negative (O2E a))
    : is_negative (a : oblique_unital_magmoid).
  Proof.
    intros b f.
    apply oblique_is_thunkable_of_envelope, H.
  Qed.

  Lemma oblique_is_positive_of_envelope (a : oblique_ob)
    (H : is_positive (O2E a))
    : is_positive (a : oblique_unital_magmoid).
  Proof.
    intros b f.
    apply oblique_is_linear_of_envelope, H.
  Qed.

  (** *** Polarities and shifts *)

  (** Polarity mapping *)
  Definition oblique_polarity_mapping : polarity_mapping oblique_unital_magmoid.
  Proof.
    apply make_polarity_mapping'; intro a.
    induction a as [n | p].
    - left.
      abstract (apply oblique_is_negative_of_envelope,
                 is_negative_envelope_ob_of_negative).
    - right.
      abstract (apply oblique_is_positive_of_envelope,
                 is_positive_envelope_ob_of_positive).
  Defined.

  (** Negative shifts *)
  Definition oblique_upshift (a : oblique_ob) : oblique_ob
    := oblique_ob_of_negative (envelope_negative_ob θ (O2E a)).

  Definition oblique_force (a : oblique_ob)
    : oblique_unital_magmoid∣_l∣⟦oblique_upshift a, a⟧.
  Proof.
    use make_submm_mor.
    - exact (force (O2E a)).
    - apply oblique_is_linear_of_envelope.
      apply (submm_mor_property _l).
  Defined.

  Definition oblique_delay (a : oblique_ob)
    : oblique_unital_magmoid∣_l∣⟦a, oblique_upshift a⟧.
  Proof.
    use make_submm_mor.
    - exact (delay (O2E a)).
    - apply oblique_is_linear_of_envelope.
      apply (submm_mor_property _l).
  Defined.

  Definition oblique_negative_shift_data
    : negative_shift_data oblique_unital_magmoid.
  Proof.
    use make_negative_shift_data.
    - exact oblique_upshift.
    - exact oblique_force.
  Defined.

  Lemma oblique_negative_shift_axioms
    : negative_shift_axioms oblique_negative_shift_data.
  Proof.
    use make_negative_shift_axioms.
    - intro a; apply (submm_mor_property _l).
    - intro a; cbn in a.
      apply oblique_is_negative_of_envelope.
      apply (sub_ob_property ^⊖ ⇑(O2E a)).
    - intro a; cbn in a.
      use make_has_submm_inverse.
      + exact (oblique_delay a).
      + exact (force (O2E a)).
  Defined.

  Lemma oblique_has_negative_shifts
    : has_negative_shifts oblique_unital_magmoid.
  Proof.
    use make_has_negative_shifts.
    - exact oblique_negative_shift_data.
    - exact oblique_negative_shift_axioms.
  Defined.

  (** Positive shifts *)
  Definition oblique_downshift (a : oblique_ob) : oblique_ob
    := oblique_ob_of_positive (envelope_positive_ob θ (O2E a)).

  Definition oblique_wrap (a : oblique_ob)
    : oblique_unital_magmoid∣_t∣⟦a, oblique_downshift a⟧.
  Proof.
    use make_submm_mor.
    - exact (wrap (O2E a)).
    - apply oblique_is_thunkable_of_envelope.
      apply (submm_mor_property _t).
  Defined.

  Definition oblique_unwrap (a : oblique_ob)
    : oblique_unital_magmoid∣_t∣⟦oblique_downshift a, a⟧.
  Proof.
    use make_submm_mor.
    - exact (unwrap (O2E a)).
    - apply oblique_is_thunkable_of_envelope.
      apply (submm_mor_property _t).
  Defined.

  Definition oblique_positive_shift_data
    : positive_shift_data oblique_unital_magmoid.
  Proof.
    use make_positive_shift_data.
    - exact oblique_downshift.
    - exact oblique_wrap.
  Defined.

  Lemma oblique_positive_shift_axioms
    : positive_shift_axioms oblique_positive_shift_data.
  Proof.
    use make_positive_shift_axioms.
    - intro a; apply (submm_mor_property _t).
    - intro a; cbn in a.
      apply oblique_is_positive_of_envelope.
      apply (sub_ob_property ^⊕ ⇓(O2E a)).
    - intro a; cbn in a.
      use make_has_submm_inverse.
      + exact (oblique_unwrap a).
      + exact (wrap (O2E a)).
  Defined.

  Lemma oblique_has_positive_shifts
    : has_positive_shifts oblique_unital_magmoid.
  Proof.
    use make_has_positive_shifts.
    - exact oblique_positive_shift_data.
    - exact oblique_positive_shift_axioms.
  Defined.

  (** Combined *)
  Lemma oblique_has_polarity_shifts
    : has_polarity_shifts oblique_unital_magmoid.
  Proof.
    use make_has_polarity_shifts.
    - exact oblique_has_negative_shifts.
    - exact oblique_has_positive_shifts.
  Defined.

  Definition oblique_preduploid : split_preduploid.
  Proof.
    use make_split_preduploid.
    - exact oblique_unital_magmoid.
    - exact oblique_polarity_mapping.
  Defined.

  Definition oblique_duploid : split_duploid.
  Proof.
    use make_split_duploid.
    - exact oblique_preduploid.
    - exact oblique_has_polarity_shifts.
    - split; intro a; now induction a.
  Defined.

  Coercion oblique_ob_to_ob (a : oblique_ob) : ob oblique_duploid := a.

  (** *** Equivalence between oblique and envelope duploid *)

  Definition oblique_to_envelope : functor oblique_duploid Env.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact oblique_to_envelope_ob.
      + intros a b; exact (idfun _).
    - easy.
  Defined.

  Definition fully_faithful_oblique_to_envelope : fully_faithful oblique_to_envelope.
  Proof. intros a b; exact (idisweq _). Defined.

  Theorem eso_oblique_to_envelope
    : submm_essentially_surjective oblique_to_envelope _lt.
  Proof.
    intros a; cbn in a.
    refine (hinhfun _ (polarity_of Env a)).
    intro H; induction H as [Hnegative | Hpositive].
    - exists (oblique_ob_of_negative (envelope_negative_ob θ a)).
      apply (weq_negative_lt_iso Env (⇑a) (a,, Hnegative)).
      exact (force a).
    - exists (oblique_ob_of_positive (envelope_positive_ob θ a)).
      apply (weq_positive_lt_iso Env (⇓a) (a,, Hpositive)).
      exact (unwrap a).
  Defined.

  Theorem split_eso_oblique_to_envelope_from_LEM (lem : LEM)
    : submm_split_essentially_surjective oblique_to_envelope _lt.
  Proof.
    intros a; cbn in a.
    induction (lem (ish_negative a)) as [Hnegative | Hpositive].
    - exists (oblique_ob_of_negative (envelope_negative_ob θ a)).
      apply (weq_negative_lt_iso Env (⇑a) (a,, Hnegative)).
      exact (force a).
    - apply (λ x, hinhuniv (invmap (weqii2withneg (ish_positive _) x)) (polarity_of Env a)) in Hpositive.
      exists (oblique_ob_of_positive (envelope_positive_ob θ a)).
      apply (weq_positive_lt_iso Env (⇓a) (a,, Hpositive)).
      exact (unwrap a).
  Defined.

  Lemma oblique_is_linear_iff_envelope {a b : oblique_ob}
    (f : oblique_duploid⟦a, b⟧)
    : is_linear (f : Env⟦O2E a, O2E b⟧) ≃ is_linear f.
  Proof.
    use weqimplimpl.
    - apply oblique_is_linear_of_envelope.
    - intro H.
      change (ob oblique_duploid) in a, b.
      apply is_linear_of_force_unwrap.
      assert (H' := assoc'_linear (M:=oblique_duploid) f H (unwrap _) (force ⇓_)).
      exact_no_check H'. (* This computation is really slow! *)
    - apply isaprop_is_linear.
    - apply isaprop_is_linear.
  Qed.

  Lemma oblique_is_thunkable_iff_envelope {a b : oblique_ob}
    (f : oblique_duploid⟦a, b⟧)
    : is_thunkable (f : Env⟦O2E a, O2E b⟧) ≃ is_thunkable f.
  Proof.
    use weqimplimpl.
    - apply oblique_is_thunkable_of_envelope.
    - intro H.
      change (ob oblique_duploid) in a, b.
      apply is_thunkable_of_delay_wrap.
      assert (H' := assoc_thunkable (M:=oblique_duploid) f H (delay _) (wrap ⇑_)).
      exact_no_check H'. (* This computation is really slow! *)
    - apply isaprop_is_thunkable.
    - apply isaprop_is_thunkable.
  Qed.

  Lemma oblique_is_negative_iff_envelope (a : oblique_ob)
    : is_negative (O2E a) ≃ is_negative (a : oblique_unital_magmoid).
  Proof.
    use weqimplimpl.
    - apply oblique_is_negative_of_envelope.
    - intro H; apply is_negative_iff_thunkable_force.
      assert (H' := is_thunkable_force_of_negative (D:=oblique_duploid) a H).
      apply oblique_is_thunkable_iff_envelope in H'.
      exact H'.
    - apply isaprop_is_negative.
    - apply isaprop_is_negative.
  Qed.

  Lemma oblique_is_positive_iff_envelope (a : oblique_ob)
    : is_positive (O2E a) ≃ is_positive (a : oblique_unital_magmoid).
  Proof.
    use weqimplimpl.
    - apply oblique_is_positive_of_envelope.
    - intro H; apply is_positive_iff_linear_wrap.
      assert (H' := is_linear_wrap_of_positive (D:=oblique_duploid) a H).
      apply oblique_is_linear_iff_envelope in H'.
      exact H'.
    - apply isaprop_is_positive.
    - apply isaprop_is_positive.
  Qed.

  (** ** Lemmas about the oblique duploid
   *** Characterization of polarities *)

  Lemma is_linear_from_upshift_iff_oblique_counit_precompose {a : N} {b : oblique_ob}
    (f : oblique_duploid⟦oblique_ob_of_negative a, b⟧)
    : is_oblique_mor_linear θ f ≃ is_linear f.
  Proof.
    exact (weqcomp (is_linear_from_upshift_iff_envelope_counit_precompose θ f)
             (oblique_is_linear_iff_envelope f)).
  Qed.

  Lemma weq_oblique_linear_mor_oblique_linear_mor (n : N) (a : oblique_ob)
    : oblique_linear_mor θ n (envelope_negative_ob θ (O2E a))
        ≃ oblique_duploid∣_l∣⟦oblique_ob_of_negative n, a⟧.
  Proof.
    apply weqfibtototal; intro f.
    apply is_linear_from_upshift_iff_oblique_counit_precompose.
  Defined.

  Lemma is_thunkable_from_downshift_iff_oblique_unit_postcompose {a : oblique_ob} {b : P}
    (f : oblique_duploid⟦a, oblique_ob_of_positive b⟧)
    : is_oblique_mor_thunkable θ f ≃ is_thunkable f.
  Proof.
    exact (weqcomp (is_thunkable_from_downshift_iff_envelope_unit_postcompose θ f)
             (oblique_is_thunkable_iff_envelope f)).
  Qed.

  Lemma weq_oblique_thunkable_mor_oblique_thunkable_mor {a : oblique_ob} {p : P}
    : oblique_thunkable_mor θ (envelope_positive_ob θ (O2E a)) p
        ≃ oblique_duploid∣_t∣⟦a, oblique_ob_of_positive p⟧.
  Proof.
    apply weqfibtototal; intro f.
    apply is_thunkable_from_downshift_iff_oblique_unit_postcompose.
  Defined.

  (** *** Inclusion functors *)

  Lemma is_negative_oblique_ob_of_negative (n : N)
    : is_negative (M:=oblique_unital_magmoid) (oblique_ob_of_negative n).
  Proof.
    apply oblique_is_negative_of_envelope, is_negative_envelope_ob_of_negative.
  Qed.

  Lemma is_positive_oblique_ob_of_positive (p : P)
    : is_positive (M:=oblique_unital_magmoid) (oblique_ob_of_positive p).
  Proof.
    apply oblique_is_positive_of_envelope, is_positive_envelope_ob_of_positive.
  Qed.

  Lemma oblique_mor_from_negative_mor {a b : N}
    (f : a --> b)
    : oblique_duploid∣_lt∣⟦oblique_ob_of_negative a, oblique_ob_of_negative b⟧.
  Proof.
    use submm_mor_from_left.
    - use weq_oblique_linear_mor_oblique_linear_mor.
      exact (oblique_lift_negative θ f).
    - apply is_thunkable_of_negative, is_negative_oblique_ob_of_negative.
  Defined.

  Lemma oblique_mor_from_positive_mor {a b : P}
    (f : a --> b)
    : oblique_duploid∣_lt∣⟦oblique_ob_of_positive a, oblique_ob_of_positive b⟧.
  Proof.
    use submm_mor_from_right.
    - use weq_oblique_thunkable_mor_oblique_thunkable_mor.
      exact (oblique_lift_positive θ f).
    - apply is_linear_of_positive, is_positive_oblique_ob_of_positive.
  Defined.

  Definition negative_to_oblique_duploid_data
    : functor_data N oblique_duploid⁻ᶜₗ.
  Proof.
    use make_functor_data.
    - intro n.
      now exists (oblique_ob_of_negative n).
    - intros a b f.
      exact (oblique_mor_from_negative_mor f).
  Defined.

  Lemma negative_to_oblique_duploid_is_functor
    : is_functor negative_to_oblique_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      apply submm_mor_eq;
      apply oblique_mor_positive_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_postcomposition, pathsinv0, id_right.
  Qed.

  Definition negative_to_oblique_duploid : N ⟶ oblique_duploid⁻ᶜₗ
    := make_functor _ negative_to_oblique_duploid_is_functor.

  Lemma isweq_on_ob_negative_to_oblique_duploid
    : isweq negative_to_oblique_duploid.
  Proof.
    use isweq_iso.
    - intros [a Ha].
      induction a as [n | p]; cbn in Ha.
      + exact n.
      + apply fromempty, nopathstruetofalse, Ha.
    - easy.
    - intros [a Ha].
      induction a as [n | p]; cbn in Ha |- *.
      + apply pair_path_in2, uip, isasetbool.
      + apply fromempty, nopathstruetofalse, Ha.
  Defined.

  Definition positive_to_oblique_duploid_data
    : functor_data P oblique_duploid⁺ᶜₜ.
  Proof.
    use make_functor_data.
    - intro p.
      now exists (oblique_ob_of_positive p).
    - intros a b f.
      exact (oblique_mor_from_positive_mor f).
  Defined.

  Lemma positive_to_oblique_duploid_is_functor
    : is_functor positive_to_oblique_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      apply submm_mor_eq;
      apply oblique_mor_negative_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_precomposition, pathsinv0, id_left.
  Qed.

  Definition positive_to_oblique_duploid : P ⟶ oblique_duploid⁺ᶜₜ
    := make_functor _ positive_to_oblique_duploid_is_functor.

  Lemma isweq_on_ob_positive_to_oblique_duploid
    : isweq positive_to_oblique_duploid.
  Proof.
    use isweq_iso.
    - intros [a Ha].
      induction a as [n | p]; cbn in Ha.
      + apply fromempty, nopathsfalsetotrue, Ha.
      + exact p.
    - easy.
    - intros [a Ha].
      induction a as [n | p]; cbn in Ha |- *.
      + apply fromempty, nopathsfalsetotrue, Ha.
      + apply pair_path_in2, uip, isasetbool.
  Defined.

End oblique_dupl.
