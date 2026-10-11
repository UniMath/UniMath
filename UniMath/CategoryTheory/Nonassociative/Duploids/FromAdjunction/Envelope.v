(********************************************************************************

 The (Single-Sorted) Duploid arising from an Adjunction

 Author: B. Szilvasy
 January–October 2026

 This file defines the envelope duploid and some proofs about it.

 Contents:
 1. Definition of the envelope duploid
 1.1. Polarity choices and their universal properties
 1.2. Envelope unital magmoid
 1.3. Envelope preduploid
 1.4. Envelope duploid
 2. Lemmas about the envelope duploid
 2.1. Characterization of polarities
 2.2. Functors into the envelope duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.ObliqueMor.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope oblique_mor.
Local Open Scope duploid.

Section envelope_defs.
  (** ** Definition of the envelope duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** A pre-object of the envelope. *)
  Definition envelope_preob := ∑ (pn : P × N), oblique_mor θ (pr1 pn) (pr2 pn).
  Definition make_envelope_preob
    (p : P) (n : N) (cross : oblique_mor θ p n)
    : envelope_preob := (p,,n),,cross.

  Definition envelope_negative_ob (a : envelope_preob) : N := pr21 a.
  Definition envelope_positive_ob (a : envelope_preob) : P := pr11 a.

  Local Notation "'π⊖'" := envelope_negative_ob (at level 1) : duploid.
  Local Notation "'π⊕'" := envelope_positive_ob (at level 1) : duploid.

  Definition envelope_mor (a b : envelope_preob) : UU := oblique_mor θ (π⊕ a) (π⊖ b).
  Definition envelope_cross_mor (a : envelope_preob) : envelope_mor a a := pr2 a.
  Local Notation "'cross(' a ')'" :=
    (envelope_cross_mor a)
      (at level 3, format "cross( a )") : duploid.

  Arguments envelope_mor / _ _.

  (** *** Polarity choices and their universal properties *)

  Definition envelope_chosen_negative (a : envelope_preob) : UU := is_z_isomorphism cross(a)♯.
  Identity Coercion Id_envelope_chosen_negative : envelope_chosen_negative >-> is_z_isomorphism.
  Definition envelope_chosen_positive (a : envelope_preob) : UU := is_z_isomorphism cross(a)♭.
  Identity Coercion Id_envelope_chosen_positive : envelope_chosen_positive >-> is_z_isomorphism.
  Definition envelope_polarization_choice (a : envelope_preob) : UU
    := envelope_chosen_negative a ⨿ envelope_chosen_positive a.

  Arguments envelope_chosen_negative / _.
  Arguments envelope_chosen_positive / _.

  Lemma isaprop_envelope_chosen_negative (a : envelope_preob)
    : isaprop (envelope_chosen_negative a).
  Proof. apply isaprop_is_z_isomorphism. Qed.
  Lemma isaprop_envelope_chosen_positive (a : envelope_preob)
    : isaprop (envelope_chosen_positive a).
  Proof. apply isaprop_is_z_isomorphism. Qed.

  (** Factoring around negative objects *)

  Definition envelope_factor_negative {a b : envelope_preob}
    (negative : envelope_chosen_negative b) (f : envelope_mor a b)
    : π⊕ a --> π⊕ b := f♯ · is_z_isomorphism_mor negative.

  Local Notation "f '◅[' H ']'" := (envelope_factor_negative H f) (format "f ◅[ H ]", at level 10).
  Local Notation "f '◅'" := (envelope_factor_negative _ f) (format "f ◅", only printing, at level 1).

  Lemma envelope_factor_negative_eq {a b : envelope_preob}
    (negative : envelope_chosen_negative b) (f : envelope_mor a b)
    : f◅[negative] ◅· cross(b) = f.
  Proof.
    apply oblique_mor_positive_path.
    refine (assoc' _ _ _ @ _ @ id_right _).
    apply cancel_precomposition, (is_inverse_in_precat2 negative).
  Qed.

  Lemma envelope_factor_negative_unique {a b : envelope_preob}
    (negative : envelope_chosen_negative b) (f : envelope_mor a b)
    (f' : π⊕ a --> π⊕ b) (H : f' ◅· cross(b) = f)
    : f' = f◅[negative].
  Proof.
    apply (maponpaths (λ x, x◅[negative])) in H.
    refine (_ @ H).
    apply pathsinv0.
    unfold envelope_factor_negative; cbn.
    etrans; [apply assoc'|].
    apply remove_id_right; [|reflexivity].
    apply (is_inverse_in_precat1 negative).
  Qed.

  Lemma envelope_factor_negative_weq {a b : envelope_preob}
    (negative : envelope_chosen_negative b)
    : (π⊕ a --> π⊕ b) ≃ (envelope_mor a b).
  Proof.
    use make_weq.
    - intro f'; exact (f' ◅· cross(b)).
    - intro f.
      use unique_exists.
      + exact (envelope_factor_negative negative f).
      + apply envelope_factor_negative_eq.
      + intro; apply isaset_oblique_mor.
      + apply envelope_factor_negative_unique.
  Qed.

  (** Factoring around positive objects *)

  Definition envelope_factor_positive {a b : envelope_preob}
    (positive : envelope_chosen_positive a) (f : envelope_mor a b)
    : π⊖ a --> π⊖ b := is_z_isomorphism_mor positive · f♭.

  Local Notation "f '▻[' H ']'" := (envelope_factor_positive H f) (format "f ▻[ H ]", at level 10).
  Local Notation "f '▻'" := (envelope_factor_positive _ f) (format "f ▻", only printing, at level 1).

  Lemma envelope_factor_positive_eq {a b : envelope_preob}
    (positive : envelope_chosen_positive a) (f : envelope_mor a b)
    : f▻[positive] ▻∘ cross(a) = f.
  Proof.
    apply oblique_mor_negative_path.
    refine (assoc _ _ _ @ _ @ id_left _).
    apply cancel_postcomposition, (is_inverse_in_precat1 positive).
  Qed.

  Lemma envelope_factor_positive_unique {a b : envelope_preob}
    (positive : envelope_chosen_positive a) (f : envelope_mor a b)
    (f' : π⊖ a --> π⊖ b) (H : f' ▻∘ cross(a) = f)
    : f' = f▻[positive].
  Proof.
    apply (maponpaths (λ x, x▻[positive])) in H.
    refine (_ @ H).
    apply pathsinv0.
    unfold envelope_factor_positive; cbn.
    etrans; [apply assoc|].
    apply remove_id_left; [|reflexivity].
    apply (is_inverse_in_precat2 positive).
  Qed.

  Lemma envelope_factor_positive_weq {a b : envelope_preob}
    (positive : envelope_chosen_positive a)
    : (π⊖ a --> π⊖ b) ≃ (envelope_mor a b).
  Proof.
    use make_weq.
    - intro f'; exact (f' ▻∘ cross(a)).
    - intro f.
      use unique_exists.
      + exact (envelope_factor_positive positive f).
      + apply envelope_factor_positive_eq.
      + intro; apply isaset_oblique_mor.
      + apply envelope_factor_positive_unique.
  Qed.

  (** *** Envelope unital magmoid *)

  (** To compose two morphisms, we need a choice of polarization for the middle object. *)
  Definition envelope_compose' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (choice : envelope_polarization_choice b)
    : envelope_mor a c.
  Proof.
    unfold envelope_mor in *.
    induction choice as [Hnegative | Hpositive].
    - exact (f◅[Hnegative] ◅· g).
    - exact (f ·▻ g▻[Hpositive]).
  Defined.

  Definition envelope_compose_id_left {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice a)
    : envelope_compose' cross(a) f choice = f.
  Proof.
    induction choice as [Hnegative | Hpositive]; cbn.
    - intermediate_path (identity _ ◅· f).
      + refine (maponpaths (λ x, x ◅· _) _).
        apply pathsinv0, envelope_factor_negative_unique.
        apply oblique_compose_positive_identity.
      + apply oblique_compose_positive_identity.
    - apply envelope_factor_positive_eq.
  Qed.

  Definition envelope_compose_id_right {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice b)
    : envelope_compose' f cross(b) choice = f.
  Proof.
    induction choice as [Hnegative | Hpositive]; cbn.
    - apply envelope_factor_negative_eq.
    - intermediate_path (identity _ ▻∘ f).
      + refine (maponpaths (λ x, x ▻∘ _) _).
        apply pathsinv0, envelope_factor_positive_unique.
        apply oblique_compose_negative_identity.
      + apply oblique_compose_negative_identity.
  Qed.

  (** However, if both choices exist, then it does not matter which we choose. *)
  Theorem envelope_compose_irrel {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (negative : envelope_chosen_negative b)
    (positive : envelope_chosen_positive b)
    : envelope_compose' f g (ii2 positive) = envelope_compose' f g (ii1 negative).
  Proof.
    change (f ·▻ g▻[positive] = f◅[negative] ◅· g).
    intermediate_path ((f◅[negative] ◅· cross(b)) ·▻ g▻[positive]).
    - refine (maponpaths (λ x, x ·▻ _) _).
      apply pathsinv0, envelope_factor_negative_eq.
    - refine (oblique_compose_negative_positive_comm _ _ _ _ @ _).
      refine (maponpaths (λ x, _ ◅· x) _).
      apply envelope_factor_positive_eq.
  Qed.

  Corollary envelope_compose_irrel' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (choice1 choice2 : envelope_polarization_choice b)
    : envelope_compose' f g choice1 = envelope_compose' f g choice2.
  Proof.
    induction choice1, choice2.
    1, 4: apply maponpaths, maponpaths, proofirrelevance, isaprop_is_z_isomorphism.
    - apply pathsinv0, envelope_compose_irrel.
    - apply envelope_compose_irrel.
  Qed.

  (** This justifies truncating the polarization choice to a property *)
  Definition envelope_polarization (a : envelope_preob) : hProp
    := ∥envelope_polarization_choice a∥.

  Lemma isaprop_envelope_polarization (a : envelope_preob) : isaprop (envelope_polarization a).
  Proof. apply propproperty. Qed.

  Definition envelope_compose {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (polarization : envelope_polarization b)
    : envelope_mor a c.
  Proof.
    refine (squash_to_set _ (envelope_compose' f g) _ polarization).
    - abstract (apply isaset_oblique_mor).
    - apply envelope_compose_irrel'.
  Defined.

  Lemma envelope_polarization_rec {a : envelope_preob}
    (T : envelope_polarization a -> hProp)
    (Hnegative : ∏ (negative : envelope_chosen_negative a), T (hinhpr (ii1 negative)))
    (Hpositive : ∏ (positive : envelope_chosen_positive a), T (hinhpr (ii2 positive)))
    : ∏ (polarization : envelope_polarization a), T polarization.
  Proof.
    intro polarization; apply squash_rec; intro H.
    induction H as [Hn | Hp].
    - apply Hnegative.
    - apply Hpositive.
  Defined.

  Lemma envelope_polarization_rec' {a : envelope_preob}
    (T : envelope_polarization a -> UU)
    (Hprop : isPredicate T)
    (Hnegative : ∏ (negative : envelope_chosen_negative a), T (hinhpr (ii1 negative)))
    (Hpositive : ∏ (positive : envelope_chosen_positive a), T (hinhpr (ii2 positive)))
    : ∏ (polarization : envelope_polarization a), T polarization.
  Proof.
    apply (envelope_polarization_rec (λ H, make_hProp (T H) (Hprop H))); assumption.
  Defined.

  Lemma envelope_compose_rec {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (T : envelope_mor a c -> hProp)
    (Hnegative : ∏ negative, T (envelope_compose' f g (ii1 negative)))
    (Hpositive : ∏ positive, T (envelope_compose' f g (ii2 positive)))
    : ∏ (polarization : envelope_polarization b), T (envelope_compose f g polarization).
  Proof.
    intro polarization.
    apply (envelope_polarization_rec (λ H, T (envelope_compose f g H))).
    - apply Hnegative.
    - apply Hpositive.
  Defined.

  Lemma envelope_compose_rec' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (T : envelope_mor a c -> UU)
    (Hprop : isPredicate T)
    (Hnegative : ∏ negative, T (envelope_compose' f g (ii1 negative)))
    (Hpositive : ∏ positive, T (envelope_compose' f g (ii2 positive)))
    : ∏ (polarization : envelope_polarization b), T (envelope_compose f g polarization).
  Proof.
    apply (envelope_compose_rec _ _ (λ H, make_hProp (T H) (Hprop H))); assumption.
  Defined.

  Lemma envelope_compose_known {a b c : envelope_preob}
    (Hchoice : envelope_polarization_choice b)
    (Hpolarization : envelope_polarization b)
    (f : envelope_mor a b) (g : envelope_mor b c)
    : envelope_compose f g Hpolarization = envelope_compose' f g Hchoice.
  Proof.
    apply envelope_compose_rec'.
    1: intro; apply isaset_oblique_mor.
    all: intro; apply envelope_compose_irrel'.
  Qed.

  Definition envelope_ob := ∑ (a : envelope_preob), envelope_polarization a.
  Definition make_envelope_ob (a : envelope_preob)
    (H : envelope_polarization a) : envelope_ob
    := a,,H.

  Coercion envelope_ob_to_envelope_preob (a : envelope_ob) : envelope_preob := pr1 a.
  Coercion envelope_ob_to_envelope_polarization (a : envelope_ob) : envelope_polarization a := pr2 a.

  Definition envelope_preob_of_positive (p : P) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact p.
    - exact (L p).
    - exact (oblique_positive_identity θ p).
  Defined.

  Definition envelope_preob_of_negative (n : N) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact (R n).
    - exact n.
    - exact (oblique_negative_identity θ n).
  Defined.

  Lemma envelope_chosen_positive_of_positive (p : P)
    : envelope_chosen_positive (envelope_preob_of_positive p).
  Proof. apply is_z_isomorphism_identity. Defined.

  Lemma envelope_chosen_negative_of_negative (n : N)
    : envelope_chosen_negative (envelope_preob_of_negative n).
  Proof. apply is_z_isomorphism_identity. Defined.

  Definition envelope_ob_of_positive (p : P) : envelope_ob.
  Proof.
    use (make_envelope_ob (envelope_preob_of_positive p)).
    apply hinhpr; constructor; apply envelope_chosen_positive_of_positive.
  Defined.

  Definition envelope_ob_of_negative (n : N) : envelope_ob.
  Proof.
    use (make_envelope_ob (envelope_preob_of_negative n)).
    apply hinhpr; constructor; apply envelope_chosen_negative_of_negative.
  Defined.

  Definition envelope_ob_mor : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact envelope_ob.
    - intros a b; exact (envelope_mor a b).
  Defined.

  Definition envelope_unital_premagmoid_data : unital_premagmoid_data.
  Proof.
    use (make_precategory_data envelope_ob_mor).
    - cbn; intro a; exact cross(a).
    - cbn; intros a b c f g; exact (envelope_compose f g b).
  Defined.

  Definition envelope_is_unital_premagmoid : is_unital_premagmoid envelope_unital_premagmoid_data.
  Proof.
    split; intros a b f; cbn;
      (apply envelope_compose_rec'; [intro; apply isaset_oblique_mor | |]).
    1, 2: intro; apply envelope_compose_id_left.
    1, 2: intro; apply envelope_compose_id_right.
  Qed.

  Definition envelope_unital_premagmoid : unital_premagmoid
    := make_unital_premagmoid _ envelope_is_unital_premagmoid.

  Definition envelope_unital_magmoid : unital_magmoid.
  Proof.
    use (make_unital_magmoid envelope_unital_premagmoid).
    abstract (intros a b; apply isaset_oblique_mor).
  Defined.

  (** *** Envelope preduploid *)

  Ltac envelope_induction a
    := let a' := uconstr:(a : envelope_ob) in
       generalize (a' : envelope_polarization a');
       apply (envelope_polarization_rec' (a:=a')).

  Lemma is_positive_of_envelope_chosen_positive (a : envelope_unital_magmoid)
    (H : envelope_chosen_positive (a : envelope_ob)) : is_positive a.
  Proof.
    intros b f c d g h; cbn in c, f, g, h |- *.
    rewrite !(envelope_compose_known (ii2 H)).
    envelope_induction c.
    - intro; apply isaset_oblique_mor.
    - intro Hn; cbn.
      apply oblique_compose_negative_positive_comm.
    - intro Hp; cbn.
      refine (!oblique_compose_negative_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, _ ·▻ x) _).
      apply envelope_factor_positive_unique.
      refine (oblique_compose_negative_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, x ·▻ _) _).
      apply envelope_factor_positive_eq.
  Qed.

  Corollary is_positive_envelope_ob_of_positive (p : P)
    : is_positive (M:=envelope_unital_magmoid) (envelope_ob_of_positive p).
  Proof.
    apply is_positive_of_envelope_chosen_positive, envelope_chosen_positive_of_positive.
  Qed.

  Lemma is_negative_of_envelope_chosen_negative (a : envelope_unital_magmoid)
    (H : envelope_chosen_negative (a : envelope_ob)) : is_negative a.
  Proof.
    intros b f c d g h; cbn in c, f, g, h |- *.
    rewrite !(envelope_compose_known (ii1 H)).
    envelope_induction c.
    - intro; apply isaset_oblique_mor.
    - intro Hp; cbn.
      refine (!oblique_compose_positive_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, _ ∘◅ x) _).
      apply envelope_factor_negative_unique.
      refine (oblique_compose_positive_compose _ _ _ _ @ _).
      refine (maponpaths (λ x, x ∘◅ _) _).
      apply envelope_factor_negative_eq.
    - intro Hp; cbn.
      apply pathsinv0, oblique_compose_negative_positive_comm.
  Qed.

  Corollary is_negative_envelope_ob_of_negative (n : N)
    : is_negative (M:=envelope_unital_magmoid) (envelope_ob_of_negative n).
  Proof.
    apply is_negative_of_envelope_chosen_negative, envelope_chosen_negative_of_negative.
  Qed.

  Lemma envelope_has_polarities : has_polarities envelope_unital_magmoid.
  Proof.
    intro a; cbn in a.
    envelope_induction a.
    - intro; apply isaprop_has_polarity.
    - intro H.
      apply make_has_polarity_negative, is_negative_of_envelope_chosen_negative, H.
    - intro H.
      apply make_has_polarity_positive, is_positive_of_envelope_chosen_positive, H.
  Qed.

  Definition envelope_preduploid : preduploid :=
    make_preduploid envelope_unital_magmoid envelope_has_polarities.

  (** *** Envelope duploid *)

  Definition envelope_downshift (a : envelope_preob) : envelope_ob
    := envelope_ob_of_positive (π⊕ a).
  Definition envelope_upshift (a : envelope_preob)
    : envelope_ob := envelope_ob_of_negative (π⊖ a).

  Definition envelope_force
    (a : envelope_preob) : envelope_mor (envelope_upshift a) a.
  Proof. exact (oblique_negative_identity θ (π⊖ a)). Defined.
  Definition envelope_delay
    (a : envelope_preob) : envelope_mor a (envelope_upshift a).
  Proof. exact cross(a). Defined.

  Definition envelope_wrap
    (a : envelope_preob) : envelope_mor a (envelope_downshift a).
  Proof. exact (oblique_positive_identity θ (π⊕ a)). Defined.
  Definition envelope_unwrap
    (a : envelope_preob) : envelope_mor (envelope_downshift a) a.
  Proof. exact cross(a). Defined.

  Lemma is_linear_envelope_force (a : envelope_ob)
    : is_linear (M:=envelope_preduploid) (envelope_force a).
  Proof.
    intros b c g h; cbn in b.
    envelope_induction b.
    1: intro; apply unital_magmoid_has_homsets.
    1: intro H; apply assoc'_negative, is_negative_of_envelope_chosen_negative, H.
    intro Hp; cbn.
    rewrite !(envelope_compose_known (ii2 Hp)); cbn.
    unfold envelope_factor_negative, envelope_factor_positive; cbn.
    apply oblique_mor_positive_path; cbn.
    rewrite <- (φ_adj_inv_identity θ), <- φ_adj_inv_natural_precomp, !id_right.
    now rewrite oblique_mor_positive_transpose.
  Qed.

  Lemma is_linear_envelope_delay (a : envelope_ob)
    : is_linear (M:=envelope_preduploid) (envelope_delay a).
  Proof.
    cbn in a; envelope_induction a.
    1: intro; apply isaprop_is_linear.
    2: intro H; apply is_linear_of_positive, is_positive_of_envelope_chosen_positive, H.
    intros Hn b c g h.
    cbn in b; envelope_induction b.
    1: intro; apply unital_magmoid_has_homsets.
    1: intro H; apply assoc'_negative, is_negative_of_envelope_chosen_negative, H.
    intro Hp; cbn.
    rewrite !(envelope_compose_known (ii2 Hp)),
      !(envelope_compose_known (ii1 Hn)); cbn.
    unfold envelope_factor_negative, envelope_factor_positive; cbn.
    unfold envelope_delay; cbn.
    apply oblique_mor_positive_path; cbn.
    rewrite <- (oblique_mor_positive_transpose θ cross(a)), <- φ_adj_inv_natural_precomp.
    now rewrite !assoc', !(is_inverse_in_precat2 Hn), !id_right,
      oblique_mor_positive_transpose.
  Qed.

  Lemma is_inverse_in_precat_envelope_force_delay (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_force a) (envelope_delay a).
  Proof.
    split; cbn.
    - envelope_induction a.
      1: intro; apply isaset_oblique_mor.
      + intro Hn; cbn.
        unfold envelope_delay, envelope_force; cbn.
        unfold envelope_factor_negative, envelope_factor_positive; cbn.
        apply oblique_mor_positive_path; cbn.
        rewrite id_left.
        apply (is_inverse_in_precat2 Hn).
      + intro Hp; cbn.
        unfold envelope_delay; cbn.
        unfold envelope_factor_negative, envelope_factor_positive; cbn.
        apply oblique_mor_positive_path; cbn.
        now rewrite (is_inverse_in_precat2 Hp), functor_id, id_right.
    - unfold envelope_delay, envelope_force; cbn.
      unfold envelope_factor_negative, envelope_factor_positive; cbn.
      apply oblique_mor_positive_path; cbn.
      now rewrite !id_right.
  Qed.

  Definition has_linear_inverse_envelope_force (a : envelope_ob)
    : has_linear_inverse (M:=envelope_preduploid) (envelope_force a).
  Proof.
    use make_has_submm_inverse.
    - exact (make_submm_mor _l _ (is_linear_envelope_delay a)).
    - apply is_inverse_in_precat_envelope_force_delay.
  Defined.

  Definition envelope_negative_shift_data : negative_shift_data envelope_preduploid.
  Proof.
    use make_negative_shift_data.
    - intro a; exact (envelope_upshift (a : envelope_ob)).
    - intro a; apply (envelope_force (a : envelope_ob)).
  Defined.

  Definition envelope_negative_shift_axioms : negative_shift_axioms envelope_negative_shift_data.
  Proof.
    use make_negative_shift_axioms.
    - apply is_linear_envelope_force.
    - intro a; apply is_negative_envelope_ob_of_negative.
    - intro a; apply has_linear_inverse_envelope_force.
  Defined.

  Definition envelope_has_negative_shifts : has_negative_shifts envelope_preduploid
    := make_has_negative_shifts _ envelope_negative_shift_axioms.

  Lemma is_thunkable_envelope_wrap (a : envelope_ob)
    : is_thunkable (M:=envelope_preduploid) (envelope_wrap a).
  Proof.
    intros b c g h; cbn in b.
    envelope_induction b.
    1: intro; apply unital_magmoid_has_homsets.
    2: intro H; apply assoc_positive, is_positive_of_envelope_chosen_positive, H.
    intro Hn; cbn.
    rewrite !(envelope_compose_known (ii1 Hn)); cbn.
    unfold envelope_factor_negative, envelope_factor_positive; cbn.
    unfold envelope_wrap; cbn.
    apply oblique_mor_negative_path; cbn.
    rewrite <- (φ_adj_identity θ), <- φ_adj_natural_postcomp, !id_left.
    now rewrite oblique_mor_negative_transpose.
  Qed.

  Lemma is_thunkable_envelope_unwrap (a : envelope_ob)
    : is_thunkable (M:=envelope_preduploid) (envelope_unwrap a).
  Proof.
    cbn in a; envelope_induction a.
    1: intro; apply isaprop_is_thunkable.
    1: intro H; apply is_thunkable_of_negative, is_negative_of_envelope_chosen_negative, H.
    intros Hp b c g h.
    cbn in b; envelope_induction b.
    1: intro; apply unital_magmoid_has_homsets.
    2: intro H; apply assoc_positive, is_positive_of_envelope_chosen_positive, H.
    intro Hn; cbn.
    rewrite !(envelope_compose_known (ii1 Hn)),
      !(envelope_compose_known (ii2 Hp)); cbn.
    unfold envelope_factor_negative, envelope_factor_positive; cbn.
    unfold envelope_unwrap; cbn.
    apply oblique_mor_negative_path; cbn.
    rewrite <- (oblique_mor_negative_transpose θ cross(a)), <- φ_adj_natural_postcomp.
    now rewrite !assoc, !(is_inverse_in_precat1 Hp), !id_left,
      oblique_mor_negative_transpose.
  Qed.

  Lemma is_inverse_in_precat_envelope_unwrap_wrap (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_unwrap a) (envelope_wrap a).
  Proof.
    split; cbn.
    - envelope_induction a.
      1: intro; apply isaset_oblique_mor.
      + intro Hn; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        unfold envelope_factor_negative, envelope_factor_positive; cbn.
        apply oblique_mor_negative_path; cbn.
        now rewrite (is_inverse_in_precat1 Hn), functor_id, id_left.
      + intro Hp; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        unfold envelope_factor_negative, envelope_factor_positive; cbn.
        apply oblique_mor_negative_path; cbn.
        rewrite id_right.
        apply (is_inverse_in_precat1 Hp).
    - unfold envelope_wrap, envelope_unwrap; cbn.
      unfold envelope_factor_negative, envelope_factor_positive; cbn.
      apply oblique_mor_negative_path; cbn.
      now rewrite !id_left.
  Qed.

  Definition has_thunkable_inverse_envelope_wrap (a : envelope_ob)
    : has_thunkable_inverse (M:=envelope_preduploid) (envelope_wrap a).
  Proof.
    use make_has_submm_inverse.
    - exact (make_submm_mor _t _ (is_thunkable_envelope_unwrap a)).
    - apply is_inverse_in_precat_inv, is_inverse_in_precat_envelope_unwrap_wrap.
  Defined.

  Definition envelope_positive_shift_data : positive_shift_data envelope_preduploid.
  Proof.
    use make_positive_shift_data.
    - intro a; exact (envelope_downshift (a : envelope_ob)).
    - intro a; apply (envelope_wrap (a : envelope_ob)).
  Defined.

  Definition envelope_positive_shift_axioms : positive_shift_axioms envelope_positive_shift_data.
  Proof.
    use make_positive_shift_axioms.
    - apply is_thunkable_envelope_wrap.
    - intro a; apply is_positive_envelope_ob_of_positive.
    - intro a; apply has_thunkable_inverse_envelope_wrap.
  Defined.

  Definition envelope_has_positive_shifts : has_positive_shifts envelope_preduploid
    := make_has_positive_shifts _ envelope_positive_shift_axioms.

  Definition envelope_has_polarity_shifts : has_polarity_shifts envelope_preduploid.
  Proof.
    use make_has_polarity_shifts.
    - apply envelope_has_negative_shifts.
    - apply envelope_has_positive_shifts.
  Defined.

  Definition envelope_duploid : duploid
    := make_duploid _ envelope_has_polarity_shifts.

  Coercion envelope_ob_to_ob (a : envelope_ob) : ob envelope_duploid := a.

  (** ** Lemmas about the envelope duploid
   *** Characterization of polarities *)

  Lemma is_linear_from_upshift_iff_envelope_counit_precompose {a : N} {b : envelope_ob}
    (f : envelope_duploid⟦envelope_ob_of_negative a, b⟧)
    : is_oblique_mor_linear θ f ≃ is_linear f.
  Proof.
    eapply weqcomp; [|apply (is_linear_iff_force_unwrap (D:=envelope_duploid))].
    eapply weqcomp; [|apply invweq, (oblique_mor_negative_path_weq θ _ _)].
    cbn; unfold envelope_factor_negative, envelope_factor_positive; cbn.
    rewrite !id_left, !functor_id, !id_left, !id_right.
    exact (idweq _).
  Qed.

  Lemma weq_envelope_linear_mor_oblique_linear_mor (n : N) (a : envelope_ob)
    : oblique_linear_mor θ n (π⊖ a) ≃ envelope_ob_of_negative n -->{_l} a.
  Proof.
    apply weqfibtototal; intro f.
    apply is_linear_from_upshift_iff_envelope_counit_precompose.
  Defined.

  Lemma is_linear_iff_from_envelope_chosen_negative {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    (Hn : envelope_chosen_negative a)
    : is_oblique_mor_linear θ
        (oblique_compose_positive _ (is_z_isomorphism_mor Hn) f)
        ≃ is_linear f.
  Proof.
    intermediate_weq (is_oblique_mor_linear θ (force a · f)). {
      apply eqweqmap, maponpaths; cbn.
      rewrite (envelope_compose_known (ii1 Hn)).
      cbn; unfold envelope_factor_negative, envelope_factor_positive; cbn.
      now rewrite id_left.
    }
    intermediate_weq (is_linear (force a · f)). {
      apply is_linear_from_upshift_iff_envelope_counit_precompose.
    }
    use weqimplimpl.
    3,4: apply isaprop_is_linear.
    - intro H.
      rewrite <- (delay_force_left f).
      exact (is_linear_compose (delay a) _ ummsolve H).
    - intro H.
      exact (is_linear_compose (force a) _ ummsolve H).
  Qed.

  Lemma is_linear_iff_envelope_impl {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    : (∏ (Hn : envelope_chosen_negative a),
        is_oblique_mor_linear θ
          (oblique_compose_positive _ (is_z_isomorphism_mor Hn) f))
        ≃ is_linear f.
  Proof.
    envelope_induction a.
    - intro; apply isapropweqtoprop, isaprop_is_linear.
    - intro Hn.
      eapply weqcomp; [|apply (is_linear_iff_from_envelope_chosen_negative _ Hn)].
      pose (c := iscontraprop1 (isaprop_envelope_chosen_negative a) Hn).
      exact (weqsecovercontr _ c).
    - intro Hp.
      apply weqimplimpl.
      + intros _.
        apply is_linear_of_positive, is_positive_of_envelope_chosen_positive, Hp.
      + intros _ Hn.
        apply is_linear_iff_from_envelope_chosen_negative.
        apply is_linear_of_positive, is_positive_of_envelope_chosen_positive, Hp.
      + apply impred; intro; apply isaprop_is_oblique_mor_linear.
      + apply isaprop_is_linear.
  Qed.

  Lemma is_positive_envelope_upshift_iff_pre_fixed_point (a : N)
    : is_negative_pre_fixed_point θ a ≃ is_positive (envelope_ob_of_negative a).
  Proof.
    eapply weqcomp; [|apply (is_positive_iff_linear_wrap (D:=envelope_duploid))].
    eapply weqcomp; [|apply is_linear_from_upshift_iff_envelope_counit_precompose].
    cbn.
    rewrite !id_right.
    exact (idweq _).
  Qed.

  Lemma is_positive_iff_from_envelope_chosen_negative (a : envelope_ob)
    (Hn : envelope_chosen_negative a)
    : is_negative_pre_fixed_point θ (π⊖ a) ≃ is_positive a.
  Proof.
    intermediate_weq (is_positive (⇑a)). {
      apply is_positive_envelope_upshift_iff_pre_fixed_point.
    }
    apply weq_is_positive_of_lt_iso, lt_iso_upshift_of_negative.
    apply is_negative_of_envelope_chosen_negative, Hn.
  Qed.

  Lemma is_thunkable_from_downshift_iff_envelope_unit_postcompose {a : envelope_ob} {b : P}
    (f : envelope_duploid⟦a, envelope_ob_of_positive b⟧)
    : is_oblique_mor_thunkable θ f ≃ is_thunkable f.
  Proof.
    eapply weqcomp; [|apply (is_thunkable_iff_delay_wrap (D:=envelope_duploid))].
    eapply weqcomp; [|apply invweq, (oblique_mor_positive_path_weq θ _ _)].
    cbn; unfold envelope_factor_negative, envelope_factor_positive; cbn.
    fold R L η.
    rewrite !id_right, !functor_id, !id_right, !id_left.
    exact (idweq _).
  Qed.

  Lemma weq_envelope_thunkable_mor_oblique_thunkable_mor (a : envelope_ob) (p : P)
    : oblique_thunkable_mor θ (π⊕ a) p ≃ a -->{_t} envelope_ob_of_positive p.
  Proof.
    apply weqfibtototal; intro f.
    apply is_thunkable_from_downshift_iff_envelope_unit_postcompose.
  Defined.

  Lemma is_thunkable_iff_from_envelope_chosen_positive {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    (Hp : envelope_chosen_positive b)
    : is_oblique_mor_thunkable θ
        (oblique_compose_negative _ f (is_z_isomorphism_mor Hp))
        ≃ is_thunkable f.
  Proof.
    intermediate_weq (is_oblique_mor_thunkable θ (f · wrap b)). {
      apply eqweqmap, maponpaths; cbn.
      rewrite (envelope_compose_known (ii2 Hp)).
      cbn; unfold envelope_factor_negative, envelope_factor_positive; cbn.
      now rewrite id_right.
    }
    intermediate_weq (is_thunkable (f · wrap b)). {
      apply is_thunkable_from_downshift_iff_envelope_unit_postcompose.
    }
    use weqimplimpl.
    3,4: apply isaprop_is_thunkable.
    - intro H.
      rewrite <- (wrap_unwrap_right f).
      exact (is_thunkable_compose _ (unwrap b) H ummsolve).
    - intro H.
      exact (is_thunkable_compose _ (wrap b) H ummsolve).
  Qed.

  Lemma is_thunkable_iff_envelope_impl {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    : (∏ (Hp : envelope_chosen_positive b),
        is_oblique_mor_thunkable θ
          (oblique_compose_negative _ f (is_z_isomorphism_mor Hp)))
        ≃ is_thunkable f.
  Proof.
    envelope_induction b.
    - intro; apply isapropweqtoprop, isaprop_is_thunkable.
    - intro Hn.
      apply weqimplimpl.
      + intros _.
        apply is_thunkable_of_negative, is_negative_of_envelope_chosen_negative, Hn.
      + intros _ Hp.
        apply is_thunkable_iff_from_envelope_chosen_positive.
        apply is_thunkable_of_negative, is_negative_of_envelope_chosen_negative, Hn.
      + apply impred; intro; apply isaprop_is_oblique_mor_thunkable.
      + apply isaprop_is_thunkable.
    - intro Hp.
      eapply weqcomp; [|apply (is_thunkable_iff_from_envelope_chosen_positive _ Hp)].
      pose (c := iscontraprop1 (isaprop_envelope_chosen_positive b) Hp).
      exact (weqsecovercontr _ c).
  Qed.

  Lemma is_negative_envelope_downshift_iff_pre_fixed_point (a : P)
    : is_positive_pre_fixed_point θ a ≃ is_negative (envelope_ob_of_positive a).
  Proof.
    eapply weqcomp; [|apply (is_negative_iff_thunkable_force (D:=envelope_duploid))].
    eapply weqcomp; [|apply is_thunkable_from_downshift_iff_envelope_unit_postcompose].
    cbn.
    rewrite !id_left.
    exact (idweq _).
  Qed.

  Lemma is_negative_iff_from_envelope_chosen_positive (a : envelope_ob)
    (Hp : envelope_chosen_positive a)
    : is_positive_pre_fixed_point θ (π⊕ a) ≃ is_negative a.
  Proof.
    intermediate_weq (is_negative (⇓a)). {
      apply is_negative_envelope_downshift_iff_pre_fixed_point.
    }
    apply weq_is_negative_of_lt_iso, submm_iso_inv, lt_iso_downshift_of_positive.
    apply is_positive_of_envelope_chosen_positive, Hp.
  Qed.

  Lemma envelope_mor_from_negative_mor {a b : N}
    (f : a --> b)
    : envelope_duploid∣_lt∣⟦envelope_ob_of_negative a, envelope_ob_of_negative b⟧.
  Proof.
    use submm_mor_from_left.
    - use weq_envelope_linear_mor_oblique_linear_mor.
      exact (oblique_lift_negative θ f).
    - apply is_thunkable_of_negative, is_negative_envelope_ob_of_negative.
  Defined.

  Lemma envelope_mor_from_positive_mor {a b : P}
    (f : a --> b)
    : envelope_duploid∣_lt∣⟦envelope_ob_of_positive a, envelope_ob_of_positive b⟧.
  Proof.
    use submm_mor_from_right.
    - use weq_envelope_thunkable_mor_oblique_thunkable_mor.
      exact (oblique_lift_positive θ f).
    - apply is_linear_of_positive, is_positive_envelope_ob_of_positive.
  Defined.

  (** *** Functors into the envelope duploid *)

  Definition negative_to_envelope_duploid_data
    : functor_data N envelope_duploid⁻ₗ.
  Proof.
    use make_functor_data.
    - intro n.
      exists (envelope_ob_of_negative n).
      apply is_negative_envelope_ob_of_negative.
    - intros a b f.
      exact (envelope_mor_from_negative_mor f).
  Defined.

  Lemma negative_to_envelope_duploid_is_functor
    : is_functor negative_to_envelope_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      apply submm_mor_eq;
      apply oblique_mor_positive_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_postcomposition, pathsinv0, id_right.
  Qed.

  Definition negative_to_envelope_duploid : N ⟶ envelope_duploid⁻ₗ
    := make_functor _ negative_to_envelope_duploid_is_functor.

  Lemma split_eso_negative_to_envelope_duploid
    : split_essentially_surjective negative_to_envelope_duploid.
  Proof.
    intros a; cbn -[envelope_duploid] in a.
    exists (π⊖ (sub_ob_ob a : envelope_ob)).
    apply weq_submm_iso_z_iso.
    change (⇑a ≅{_lt} a).
    apply weq_negative_lt_iso.
    exact (force a).
  Defined.

  Definition positive_to_envelope_duploid_data
    : functor_data P envelope_duploid⁺ₜ.
  Proof.
    use make_functor_data.
    - intro p.
      exists (envelope_ob_of_positive p).
      apply is_positive_envelope_ob_of_positive.
    - intros a b f.
      exact (envelope_mor_from_positive_mor f).
  Defined.

  Lemma positive_to_envelope_duploid_is_functor
    : is_functor positive_to_envelope_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      apply submm_mor_eq;
      apply oblique_mor_negative_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_precomposition, pathsinv0, id_left.
  Qed.

  Definition positive_to_envelope_duploid : P ⟶ envelope_duploid⁺ₜ
    := make_functor _ positive_to_envelope_duploid_is_functor.

  Lemma split_eso_positive_to_envelope_duploid
    : split_essentially_surjective positive_to_envelope_duploid.
  Proof.
    intros a; cbn -[envelope_duploid] in a.
    exists (π⊕ (sub_ob_ob a : envelope_ob)).
    apply weq_submm_iso_z_iso.
    change (⇓a ≅{_lt} a).
    apply weq_positive_lt_iso.
    exact (unwrap a).
  Defined.

End envelope_defs.

Ltac envelope_induction θ a
  := let a' := uconstr:(a : envelope_ob θ) in
     generalize (a' : envelope_polarization θ a');
     apply (envelope_polarization_rec' θ (a:=a')).

Notation "'π⊖'" := (envelope_negative_ob _) (at level 1) : duploid.
Notation "'π⊕'" := (envelope_positive_ob _) (at level 1) : duploid.
Notation "'cross(' a ')'" := (envelope_cross_mor _ a) (at level 3, format "cross( a )") : duploid.
