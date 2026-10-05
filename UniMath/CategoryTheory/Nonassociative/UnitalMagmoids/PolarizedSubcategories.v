(********************************************************************************

 Polarized Subcategories

 Author: B. Szilvasy
 September 2026

 We define the linear, thunkable, intermediate, positive, and negative
 subcategories of a unital magmoid.

 Contents:
 1. Linear, thunkable, intermediate, and polarized subcategories
 2. Inclusion functors
 3. Specific inverses and when they are unique
 4. Composition of inverses when they exist
 5. Linear-and-thunkable(-and-intermediate) isomorphisms [lt(i)_iso]
 6. Lemmas about isomorphisms

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** Linear, thunkable, intermediate, and polarized subcategories *)

Section polarized_submagmoids.
  Context {M : unital_magmoid}.
  Let hs : has_homsets M := unital_magmoid_has_homsets M.

  (** Linear morphisms *)
  Definition isw_linear : wide_submagmoid M
    := make_wide_submagmoid' (@ish_linear M) is_linear_identity (@is_linear_compose M).
  Definition isc_linear : wide_subcategory M
    := make_wide_subcategory isw_linear (λ a b c d f g h Hf Hg Hh, assoc_linear _ Hh _ _).

  (** Thunkable morphisms *)
  Definition isw_thunkable : wide_submagmoid M
    := make_wide_submagmoid' (@ish_thunkable M) is_thunkable_identity (@is_thunkable_compose M).
  Definition isc_thunkable : wide_subcategory M
    := make_wide_subcategory isw_thunkable (λ a b c d f g h Hf Hg Hh, assoc_thunkable _ Hf _ _).

  (** Intermediate morphisms *)
  Definition isw_intermediate : wide_submagmoid M
    := make_wide_submagmoid' (@ish_intermediate M)
         is_intermediate_identity (@is_intermediate_compose M).
  Definition isc_intermediate : wide_subcategory M
    := make_wide_subcategory isw_intermediate (λ a b c d f g h Hf Hg Hh, assoc_intermediate _ Hg _ _).

  (** Linear and thunkable (and intermediate) morphisms *)
  Definition isw_linear_and_thunkable : wide_submagmoid M
    := wide_submagmoid_intersection isw_linear isw_thunkable.
  Definition isc_linear_and_thunkable : wide_subcategory M
    := make_wide_subcategory isw_linear_and_thunkable
         (is_assoc_wide_submagmoid_intersection_left _ _
            (wide_subcategory_is_assoc isc_linear)).

  Definition isw_linear_and_thunkable_and_intermediate : wide_submagmoid M
    := wide_submagmoid_intersection isw_linear_and_thunkable isw_intermediate.
  Definition isc_linear_and_thunkable_and_intermediate : wide_subcategory M
    := make_wide_subcategory isw_linear_and_thunkable_and_intermediate
         (is_assoc_wide_submagmoid_intersection_right _ _
            (wide_subcategory_is_assoc isc_intermediate)).

End polarized_submagmoids.
Arguments isw_linear _ : clear implicits.
Arguments isc_linear _ : clear implicits.
Arguments isw_thunkable _ : clear implicits.
Arguments isc_thunkable _ : clear implicits.
Arguments isw_intermediate _ : clear implicits.
Arguments isc_intermediate _ : clear implicits.
Arguments isw_linear_and_thunkable _ : clear implicits.
Arguments isc_linear_and_thunkable _ : clear implicits.
Arguments isw_linear_and_thunkable_and_intermediate _ : clear implicits.
Arguments isc_linear_and_thunkable_and_intermediate _ : clear implicits.

Notation "'_l'" := (isc_linear _) : unital_magmoid.
Notation "'_t'" := (isc_thunkable _) : unital_magmoid.
Notation "'_i'" := (isc_intermediate _) : unital_magmoid.
Notation "'_lt'" := (isc_linear_and_thunkable _) : unital_magmoid.
Notation "'_lti'" := (isc_linear_and_thunkable_and_intermediate _) : unital_magmoid.

Section polarized_subcategories.
  Context (M : unital_magmoid).

  Definition linear_category : category := wide_subcategory_carrier M _l.
  Definition thunkable_category : category := wide_subcategory_carrier M _t.
  Definition linear_and_thunkable_category : category := wide_subcategory_carrier M _lt.
  Definition linear_and_thunkable_and_intermediate_category : category := wide_subcategory_carrier M _lti.

  Definition positive_category : category := associative_submagmoid_carrier M ^⊕ _l.
  Definition negative_category : category := associative_submagmoid_carrier M ^⊖ _t.
  Definition positive_thunkable_category : category := associative_submagmoid_carrier M ^⊕ _lt.
  Definition negative_linear_category : category := associative_submagmoid_carrier M ^⊖ _lt.

  Definition weq_positive_mor {a b : sub_ob (@ish_positive M)}
    : M⟦a, b⟧ ≃ M∣_l∣⟦a, b⟧.
  Proof.
    apply weq_make_submm_mor; intro f.
    apply is_linear_of_positive.
    exact (sub_ob_property a).
  Defined.

  Definition weq_positive_thunkable_mor {a b : sub_ob (@ish_positive M)}
    : M∣_t∣⟦a, b⟧ ≃ M∣_lt∣⟦a, b⟧.
  Proof.
    apply weq_submm_mor_incl; intro f.
    apply dirprod_with_contr_l.
    apply iscontraprop1.
    - apply propproperty.
    - apply is_linear_of_positive.
      exact (sub_ob_property a).
  Defined.

  Definition weq_negative_mor {a b : sub_ob (@ish_negative M)}
    : M⟦a, b⟧ ≃ M∣_t∣⟦a, b⟧.
  Proof.
    apply weq_make_submm_mor; intro f.
    apply is_thunkable_of_negative.
    exact (sub_ob_property b).
  Defined.

  Definition weq_negative_linear_mor {a b : sub_ob (@ish_negative M)}
    : M∣_l∣⟦a, b⟧ ≃ M∣_lt∣⟦a, b⟧.
  Proof.
    apply weq_submm_mor_incl; intro f.
    apply dirprod_with_contr_r.
    apply iscontraprop1.
    - apply propproperty.
    - apply is_thunkable_of_negative.
      exact (sub_ob_property b).
  Defined.

End polarized_subcategories.

Notation "M 'ₗ'" := (linear_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_l *)
Notation "M 'ₜ'" := (thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_t *)
Notation "M 'ₗₜ'" := (linear_and_thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_l \_t *)
Notation "M 'ₗₜᵢ'" := (linear_and_thunkable_and_intermediate_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_l \_t \_i *)
Notation "M '⁺'" := (positive_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^+ *)
Notation "M '⁻'" := (negative_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^- *)
Notation "M '⁺ₜ'" := (positive_thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^+ \_t *)
Notation "M '⁻ₗ'" := (negative_linear_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^- \_l *)

(** ** Inclusion functors

  The inclusion functors between the categories of a unital magmoid M
  are depicted in the commutative diagram below. Of these, all but
  the four vertically drawn functors are fully faithful.

  <<
                      M⁺  ⟶ Mₗ    ↰
                      ↑     ↑
                      M⁺ₜ → Mₗₜ  ← M⁻ₗ
                            ↓     ↓
                      ↳     Mₜ  ← M⁻
  >>

  All categories also have inclusion functors into M itself.

 *)
Section inclusion_functors.
  Context (M : unital_magmoid).

  (** Direct inclusions *)
  Definition positive_to_linear_category : M⁺ ⟶ M ₗ
    := submm_into_wide_incl M ^⊕ _l.
  Definition positive_thunkable_to_linear_and_thunkable_category : M⁺ₜ ⟶ M ₗₜ
    := submm_into_wide_incl M ^⊕ _lt.
  Definition positive_thunkable_to_positive_category : M⁺ₜ ⟶ M⁺
    := wide_submm_incl _
         (full_subcategory_promote M ^⊕ _lt)
         (full_subcategory_promote M ^⊕ _l)
         (λ a b f, pr1).

  Definition negative_to_thunkable_category : M⁻ ⟶ M ₜ
    := submm_into_wide_incl M ^⊖ _t.
  Definition negative_linear_to_linear_and_thunkable_category : M⁻ₗ ⟶ M ₗₜ
    := submm_into_wide_incl M ^⊖ _lt.
  Definition negative_linear_to_negative_category : M⁻ₗ ⟶ M⁻
    := wide_submm_incl _
         (full_subcategory_promote M ^⊖ _lt)
         (full_subcategory_promote M ^⊖ _t)
         (λ a b f, pr2).

  Definition linear_and_thunkable_to_linear_category : M ₗₜ ⟶ M ₗ
    := wide_submm_incl M _lt _l (λ a b f, pr1).
  Definition linear_and_thunkable_to_thunkable_category : M ₗₜ ⟶ M ₜ
    := wide_submm_incl M _lt _t (λ a b f, pr2).

  (** Composites *)
  Definition positive_thunkable_to_linear_category : M⁺ₜ ⟶ M ₗ
    := positive_thunkable_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_to_linear_category.
  Definition positive_thunkable_to_thunkable_category : M⁺ₜ ⟶ M ₜ
    := positive_thunkable_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_to_thunkable_category.
  Definition negative_linear_to_thunkable_category : M⁻ₗ ⟶ M ₜ
    := negative_linear_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_to_thunkable_category.
  Definition negative_linear_to_linear_category : M⁻ₗ ⟶ M ₗ
    := negative_linear_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_to_linear_category.

  (** Inclusions into [M] *)
  Definition linear_to_unital_magmoid : M ₗ ⟶ M
    := wide_submm_trivial_incl M _l.
  Definition thunkable_to_unital_magmoid : M ₜ ⟶ M
    := wide_submm_trivial_incl M _t.
  Definition linear_and_thunkable_to_unital_magmoid : M ₗₜ ⟶ M
    := wide_submm_trivial_incl M _lt.
  Definition positive_to_unital_magmoid : M⁺ ⟶ M
    := positive_to_linear_category ∙ linear_to_unital_magmoid.
  Definition negative_to_unital_magmoid : M⁻ ⟶ M
    := negative_to_thunkable_category ∙ thunkable_to_unital_magmoid.

  Lemma fully_faithful_positive_to_linear_category
    : fully_faithful positive_to_linear_category.
  Proof. apply fully_faithful_submm_into_wide_incl. Defined.
  Lemma fully_faithful_positive_thunkable_to_linear_and_thunkable_category
    : fully_faithful positive_thunkable_to_linear_and_thunkable_category.
  Proof. apply fully_faithful_submm_into_wide_incl. Defined.
  Lemma fully_faithful_negative_to_thunkable_category
    : fully_faithful negative_to_thunkable_category.
  Proof. apply fully_faithful_submm_into_wide_incl. Defined.
  Lemma fully_faithful_negative_linear_to_linear_and_thunkable_category
    : fully_faithful negative_linear_to_linear_and_thunkable_category.
  Proof. apply fully_faithful_submm_into_wide_incl. Defined.
  Lemma fully_faithful_negative_linear_to_thunkable_category
    : fully_faithful negative_linear_to_linear_and_thunkable_category.
  Proof. apply fully_faithful_submm_into_wide_incl. Defined.

  Lemma faithful_linear_and_thunkable_to_linear_category
    : faithful linear_and_thunkable_to_linear_category.
  Proof. apply faithful_wide_submm_incl. Defined.
  Lemma faithful_linear_and_thunkable_to_thunkable_category
    : faithful linear_and_thunkable_to_thunkable_category.
  Proof. apply faithful_wide_submm_incl. Defined.

  Lemma faithful_positive_thunkable_to_positive_category
    : faithful positive_thunkable_to_positive_category.
  Proof. apply faithful_wide_submm_incl. Defined.
  Lemma faithful_negative_linear_to_negative_category
    : faithful negative_linear_to_negative_category.
  Proof. apply faithful_wide_submm_incl. Defined.

  Definition faithful_positive_thunkable_to_linear_category
    : faithful positive_thunkable_to_linear_category.
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful,
        fully_faithful_positive_thunkable_to_linear_and_thunkable_category.
    - apply faithful_linear_and_thunkable_to_linear_category.
  Defined.

  Definition faithful_negative_linear_to_thunkable_category
    : faithful negative_linear_to_thunkable_category.
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful,
        fully_faithful_negative_linear_to_linear_and_thunkable_category.
    - apply faithful_linear_and_thunkable_to_thunkable_category.
  Defined.

  Lemma faithful_linear_to_unital_magmoid
    : faithful linear_to_unital_magmoid.
  Proof. apply faithful_wide_submm_trivial_incl. Defined.
  Lemma faithful_thunkable_to_unital_magmoid
    : faithful thunkable_to_unital_magmoid.
  Proof. apply faithful_wide_submm_trivial_incl. Defined.

  Lemma fully_faithful_positive_to_unital_magmoid
    : fully_faithful positive_to_unital_magmoid.
  Proof.
    apply fully_faithful_submm_trivial_incl.
    intros a b f.
    apply is_linear_of_positive.
    exact (sub_ob_property a).
  Defined.
  Lemma fully_faithful_negative_to_unital_magmoid
    : fully_faithful negative_to_unital_magmoid.
  Proof.
    apply fully_faithful_submm_trivial_incl.
    intros a b f.
    apply is_thunkable_of_negative.
    exact (sub_ob_property b).
  Defined.

  (** I : M⁺ₜ ⟶ M ₗ factors through M⁺ *)
  Lemma positive_thunkable_to_linear_category_through_positive
    : positive_thunkable_to_linear_category
      = (positive_thunkable_to_positive_category
           ∙ positive_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** I : M⁻ₗ ⟶ M ₜ factors through M⁻ *)
  Lemma negative_linear_to_thunkable_category_through_negative
    : negative_linear_to_thunkable_category
      = (negative_linear_to_negative_category
           ∙ negative_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** I : M⁻ₗ ⟶ M ₗ factors through M ₗₜ *)
  Lemma negative_linear_to_linear_category_through_thunkable
    : negative_linear_to_linear_category
      = (negative_linear_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** I : M⁺ₜ ⟶ M ₜ factors through M ₜₗ *)
  Lemma positive_thunkable_to_thunkable_category_through_linear
    : positive_thunkable_to_thunkable_category
      = (positive_thunkable_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

End inclusion_functors.

(** ** Specific inverses and when they are unique *)

Section inverses.
  Context {M : unital_magmoid} {a b : M} (f : a --> b).

  (* Linear inverses are unique *)
  Definition has_linear_inverse : UU := has_submm_inverse _l f.
  Identity Coercion Id_has_linear_inverse : has_linear_inverse >-> has_submm_inverse.
  (* Construct with [make_has_submm_inverse]. *)

  Lemma isaprop_has_linear_inverse : isaprop has_linear_inverse.
  Proof.
    apply isaprop_has_submm_inverse_from_assoc.
    intros c d g h Hg Hh.
    now apply assoc'_linear.
  Qed.

  (* Thunkable inverses are unique *)
  Definition has_thunkable_inverse : UU := has_submm_inverse _t f.
  Identity Coercion Id_has_thunkable_inverse : has_thunkable_inverse >-> has_submm_inverse.
  (* Construct with [make_has_submm_inverse]. *)

  Lemma isaprop_has_thunkable_inverse : isaprop has_thunkable_inverse.
  Proof.
    apply isaprop_has_submm_inverse_from_assoc.
    intros c d g h Hg Hh.
    now apply assoc'_thunkable.
  Qed.

  (* Thunkable-and-linear inverses are of course unique *)
  Definition has_linear_and_thunkable_inverse : UU := has_submm_inverse _lt f.
  Identity Coercion Id_has_linear_and_thunkable_inverse
    : has_linear_and_thunkable_inverse >-> has_submm_inverse.

  Lemma isaprop_has_linear_and_thunkable_inverse : isaprop has_linear_and_thunkable_inverse.
  Proof.
    use (isofhlevelsninclb 0 (has_submm_inverse_incl M _lt _l (λ _, pr1) f)).
    - apply isincl_has_submm_inverse_incl.
    - apply isaprop_has_linear_inverse.
  Qed.

  (* If a morphism is intermediate then its inverses are unique. *)
  Lemma isaprop_has_submm_inverse_from_intermediate
    (H : is_intermediate f)
    (P : wide_submagmoid M)
    : isaprop (has_submm_inverse P f).
  Proof.
    apply isaprop_has_submm_inverse_from_assoc.
    intros c d g h _ _.
    now apply assoc'_intermediate.
  Qed.

  Corollary isaprop_is_z_isomorphism_from_intermediate
    (H : is_intermediate f)
    : isaprop (is_z_isomorphism f).
  Proof.
    apply (isofhlevelweqf 1 (weq_has_trivial_submm_inverse_is_z_isomorphism f)).
    apply isaprop_has_submm_inverse_from_intermediate, H.
  Qed.

End inverses.

(** ** Composition of inverses when they exist *)

Section composition.
  Context {M : unital_magmoid}.

  (** There are multiple ways in which linearity and thunkability permit
      composition of inverses. *)

  Lemma is_inverse_in_magmoid_comp_2linear {a b c : M}
    (f : a --> b) (g : a <-- b) (f' : b --> c) (g' : b <-- c)
    (Hg : is_linear g) (Hg' : is_linear g')
    (H1 : f · g = identity a) (H2 : f' · g' = identity b)
    : (f · f') · (g' · g) = identity a.
  Proof.
    refine (assoc_linear _ Hg _ _ @ _ @ H1).
    apply cancel_postcomposition.
    refine (assoc'_linear _ Hg' _ _ @ _ @ magmoid_id_right f).
    apply cancel_precomposition, H2.
  Qed.

  Lemma is_inverse_in_magmoid_comp_2thunkable {a b c : M}
    (f : a <-- b) (g : a --> b) (f' : b <-- c) (g' : b --> c)
    (Hg : is_thunkable g) (Hg' : is_thunkable g')
    (H1 : f ∘ g = identity a) (H2 : f' ∘ g' = identity b)
    : (f ∘ f') ∘ (g' ∘ g) = identity a.
  Proof.
    refine (assoc'_thunkable _ Hg _ _ @ _ @ H1).
    apply cancel_precomposition.
    refine (assoc_thunkable _ Hg' _ _ @ _ @ magmoid_id_left f).
    apply cancel_postcomposition, H2.
  Qed.

  (** Linear-and-thunkable inverses compose. *)
  Lemma has_linear_and_thunkable_inverse_compose {a b c : M}
    (f : a --> b) (g : has_linear_and_thunkable_inverse f)
    (f' : b --> c) (g' : has_linear_and_thunkable_inverse f')
    : has_linear_and_thunkable_inverse (f · f').
  Proof.
    use make_has_submm_inverse.
    - apply (submm_inv_mor _ g' ·{_lt} submm_inv_mor _ g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (submm_inv_mor _ g).
        * apply (submm_inv_mor _ g').
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (submm_inv_mor _ g').
        * apply (submm_inv_mor _ g ).
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
  Defined.

  (** Linear inverses of linear maps compose -- but this is just the linear
      category. *)
  Lemma has_linear_inverse_compose {a b c : M}
    (f : a -->{_l} b) (g : has_linear_inverse f)
    (f' : b -->{_l} c) (g' : has_linear_inverse f')
    : has_linear_inverse (f · f').
  Proof.
    use make_has_submm_inverse.
    - apply (submm_inv_mor _ g' ·{_l} submm_inv_mor _ g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (submm_inv_mor _ g).
        * apply (submm_inv_mor _ g').
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply f'.
        * apply f.
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
  Defined.

  (** Thunkable inverses of thunkable maps compose -- but this is just the
      thunkable category. *)
  Lemma has_thunkable_inverse_compose {a b c : M}
    (f : a -->{_t} b) (g : has_thunkable_inverse f)
    (f' : b -->{_t} c) (g' : has_thunkable_inverse f')
    : has_thunkable_inverse (f · f').
  Proof.
    use make_has_submm_inverse.
    - apply (submm_inv_mor _ g' ·{_t} submm_inv_mor _ g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply f.
        * apply f'.
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (submm_inv_mor _ g').
        * apply (submm_inv_mor _ g).
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
  Defined.

End composition.

(** ** Linear-and-thunkable(-and-intermediate) isomorphisms [lt(i)_iso] *)

Section isos.
  Context {M : unital_magmoid}.

  Definition is_lt_iso {a b : M} (f : a --> b) : UU := is_subcat_iso _lt f.
  Identity Coercion Id_is_lt_iso : is_lt_iso >-> is_subcat_iso.
  Definition isaprop_is_lt_iso {a b : M} (f : a --> b) : isaprop (is_lt_iso f)
    := isaprop_is_subcat_iso _lt f.

  Definition lt_iso (a b : M) : UU := submm_iso _lt a b.
  Identity Coercion Id_lt_iso : lt_iso >-> submm_iso.

  Lemma lt_iso_eq {a b : M} (f g : lt_iso a b)
    : (submm_iso_plain_mor _lt f = submm_iso_plain_mor _lt g)
        ≃ f = g.
  Proof. apply subcat_iso_eq. Defined.

  Lemma isaset_lt_iso (a b : M) : isaset (lt_iso a b).
  Proof. apply isaset_submm_iso. Qed.

  Lemma lt_iso_left {a b : M} (p : lt_iso a b)
    {c : M} (f : a --> c)
    : p · (submm_iso_inv _lt p · f) = f.
  Proof.
    apply (submm_iso_left_of_thunkable _lt p).
    apply (submm_mor_property _lt).
  Qed.
  Lemma lt_iso_inv_left {a b : M} (p : lt_iso b a)
    {c : M} (f : a --> c)
    : submm_iso_inv _lt p · (p · f) = f.
  Proof.
    apply (submm_iso_left_of_inv_thunkable _lt p).
    apply (submm_mor_property _lt).
  Qed.

  Lemma lt_iso_right {a b : M} (p : lt_iso b a)
    {c : M} (f : a <-- c)
    : p ∘ (submm_iso_inv _lt p ∘ f) = f.
  Proof.
    apply (submm_iso_right_of_linear _lt p).
    apply (submm_mor_property _lt).
  Qed.
  Lemma lt_iso_inv_right {a b : M} (p : lt_iso a b)
    {c : M} (f : a <-- c)
    : submm_iso_inv _lt p ∘ (p ∘ f) = f.
  Proof.
    apply (submm_iso_right_of_inv_linear _lt p).
    apply (submm_mor_property _lt).
  Qed.

  Definition lti_iso (a b : M) : UU := submm_iso _lti a b.
  Identity Coercion Id_lti_iso : lti_iso >-> submm_iso.

  Definition lti_iso_to_lt_iso {a b : M} (f : lti_iso a b) : lt_iso a b
    := submm_iso_incl M _lti _lt ((λ _, pr1),, (λ _, pr1)) f.

  Lemma lti_iso_left {a b : M} (p : lti_iso a b)
    {c : M} (f : a --> c)
    : p · (submm_iso_inv _lti p · f) = f.
  Proof.
    apply (submm_iso_left_of_thunkable _lti p).
    apply (submm_mor_property _lti).
  Qed.
  Lemma lti_iso_inv_left {a b : M} (p : lti_iso b a)
    {c : M} (f : a --> c)
    : submm_iso_inv _lti p · (p · f) = f.
  Proof.
    apply (submm_iso_left_of_inv_thunkable _lti p).
    apply (submm_mor_property _lti).
  Qed.

  Lemma lti_iso_right {a b : M} (p : lti_iso b a)
    {c : M} (f : a <-- c)
    : p ∘ (submm_iso_inv _lti p ∘ f) = f.
  Proof.
    apply (submm_iso_right_of_linear _lti p).
    apply (submm_mor_property _lti).
  Qed.
  Lemma lti_iso_inv_right {a b : M} (p : lti_iso a b)
    {c : M} (f : a <-- c)
    : submm_iso_inv _lti p ∘ (p ∘ f) = f.
  Proof.
    apply (submm_iso_right_of_inv_linear _lti p).
    apply (submm_mor_property _lti).
  Qed.

  Lemma lti_iso_interpose {a b : M}
    (p : lti_iso a b)
    {c d : M}
    (f : c --> a)
    (g : a --> d)
    : (f · p) · (submm_inv_mor _lti p · g) = f · g.
  Proof.
    apply submm_iso_interpose_of_intermediate.
    - apply (submm_mor_property _lti).
    - apply (submm_mor_property _lti).
  Qed.
  Lemma lti_iso_interpose_inv {a b : M}
    (p : lti_iso b a)
    {c d : M}
    (f : c --> a)
    (g : a --> d)
    : (f · submm_inv_mor _lti p) · (p · g) = f · g.
  Proof.
    apply submm_iso_interpose_inv_of_intermediate.
    - apply (submm_mor_property _lti).
    - apply (submm_mor_property _lti).
  Qed.

  Lemma isaset_lti_iso {a b : M} : isaset (lti_iso a b).
  Proof. apply isaset_submm_iso. Qed.

  Definition lti_iso_eq {a b : M} (f g : lti_iso a b)
    : (submm_iso_plain_mor _lti f = submm_iso_plain_mor _lti g)
        ≃ f = g.
  Proof. apply subcat_iso_eq. Defined.

  Theorem isincl_lti_iso_to_lt_iso (a b : M)
    : isincl (@lti_iso_to_lt_iso a b).
  Proof. apply isincl_submm_iso_incl. Defined.

  Definition lti_iso_from_intermediate_lt_iso {a b : M}
    (f : lt_iso a b)
    (Hf : is_intermediate f)
    (Hfinv : is_intermediate (submm_inv_mor _lt f))
    : lti_iso a b.
  Proof.
    use make_submm_iso'.
    - apply (submm_mor_from_left f), Hf.
    - apply (submm_mor_from_left (submm_inv_mor _lt f)), Hfinv.
    - exact f.
  Defined.

End isos.

(** ** Lemmas about isomorphisms *)

Section isos_facts.
  Context {M : unital_magmoid}.

  Lemma is_intermediate_from_interpose {b b' : M}
    (p : b --> b')
    (pinv : has_thunkable_inverse p)
    (Hp : ∏ (a c : M) (f : a --> b) (g : b --> c),
        (f · p) · (submm_inv_mor _t pinv · g) = f · g)
    : is_intermediate p.
  Proof.
    intros a c f g.
    intermediate_path ((f · p) · (submm_inv_mor _t pinv · (p · g))). {
      apply pathsinv0, Hp.
    }
    rewrite (assoc_thunkable (submm_inv_mor _t pinv) (submm_mor_property _t _)).
    apply cancel_precomposition.
    refine (_ @ magmoid_id_left g).
    apply cancel_postcomposition.
    apply (is_inverse_in_precat2 pinv).
  Qed.

  Lemma lt_iso_i_from_interpose {b b' : M}
    (p : lt_iso b b')
    (Hp : ∏ (a c : M) (f : a --> b) (g : b --> c),
        (f · p) · (submm_inv_mor _lt p · g) = f · g)
    : is_submm_iso _i p.
  Proof.
    use make_is_submm_iso'.
    - exact (submm_inv_mor _lt p).
    - use (is_intermediate_from_interpose p). {
        apply (has_submm_inverse_incl M _lt _t (λ _, pr2) _ p).
      }
      apply Hp.
    - use (is_intermediate_from_interpose (submm_inv_mor _lt p)). {
        apply (has_submm_inverse_incl M _lt _t (λ _, pr2) _ (submm_iso_inv _lt p)).
      }
      intros a c f g.
      etrans; [apply pathsinv0, Hp|]; cbn.
      etrans.
      + apply cancel_postcomposition, (lt_iso_right p).
      + apply cancel_precomposition, (lt_iso_inv_left p).
    - cbn; exact p.
  Qed.

  (** [lt_iso]s preserve polarities *)

  Lemma is_positive_of_lt_iso {a b : M}
    (p : lt_iso a b) (H : is_positive a) : is_positive b.
  Proof.
    intros c f.
    rewrite <- (lt_iso_inv_left p f).
    apply is_linear_compose.
    - apply (submm_mor_property _lt).
    - apply is_linear_of_positive, H.
  Qed.

  Corollary weq_is_positive_of_lt_iso {a b : M}
    (p : lt_iso a b)
    : is_positive a ≃ is_positive b.
  Proof.
    apply weqimplimpl.
    - apply is_positive_of_lt_iso, p.
    - apply is_positive_of_lt_iso, submm_iso_inv, p.
    - apply isaprop_is_positive.
    - apply isaprop_is_positive.
  Qed.

  Lemma is_negative_of_lt_iso {a b : M}
    (p : lt_iso a b) (H : is_negative a) : is_negative b.
  Proof.
    intros c f.
    rewrite <- (lt_iso_right p f).
    apply is_thunkable_compose.
    - apply is_thunkable_of_negative, H.
    - apply (submm_mor_property _lt).
  Qed.

  Corollary weq_is_negative_of_lt_iso {a b : M}
    (p : lt_iso a b)
    : is_negative a ≃ is_negative b.
  Proof.
    apply weqimplimpl.
    - apply is_negative_of_lt_iso, p.
    - apply is_negative_of_lt_iso, submm_iso_inv, p.
    - apply isaprop_is_negative.
    - apply isaprop_is_negative.
  Qed.

  (** If anything is polarized, [lt_iso]s and [lti_iso]s merge. *)

  Lemma lt_iso_is_intermediate_from_polarized
    {a b : M}
    (p : lt_iso a b)
    (H : is_negative a ∨ is_positive a)
    : is_intermediate p.
  Proof.
    isaprop_goal Hprop; [apply isaprop_is_intermediate|].
    apply (squash_to_prop H Hprop).
    clear H; intro H; induction H as [Hnegative | Hpositive].
    - apply is_intermediate_of_negative, Hnegative.
    - apply is_intermediate_of_positive.
      apply (is_positive_of_lt_iso p Hpositive).
  Qed.

  Lemma transport_polarized_across_lt_iso {a b : M}
    (p : lt_iso a b)
    (H : is_negative a ∨ is_positive a)
    : is_negative b ∨ is_positive b.
  Proof.
    revert H; apply hinhfun; intro H.
    induction H as [Hnegative | Hpositive].
    - apply ii1, (is_negative_of_lt_iso p Hnegative).
    - apply ii2, (is_positive_of_lt_iso p Hpositive).
  Qed.

  Lemma lt_iso_is_intermediate_from_polarized'
    {a b : M}
    (p : lt_iso a b)
    (H : is_negative b ∨ is_positive b)
    : is_intermediate p.
  Proof.
    apply lt_iso_is_intermediate_from_polarized.
    apply (transport_polarized_across_lt_iso
             (submm_iso_inv _lt p) H).
  Qed.

  Lemma isweq_lti_iso_to_lt_iso_from_polarized (a b : M)
    (H : is_negative a ∨ is_positive a)
    : isweq (@lti_iso_to_lt_iso M a b).
  Proof.
    apply (isweqinclandsurj _ (isincl_lti_iso_to_lt_iso _ _)).
    intro f; apply hinhpr.
    use make_hfiber.
    - apply (lti_iso_from_intermediate_lt_iso f).
      + apply lt_iso_is_intermediate_from_polarized, H.
      + apply (lt_iso_is_intermediate_from_polarized' (submm_iso_inv _lt f)), H.
    - now apply lt_iso_eq.
  Defined.

  Definition weq_lti_iso_to_lt_iso_from_polarized (a b : M)
    (H : is_negative a ∨ is_positive a)
    : lti_iso a b ≃ lt_iso a b
    := make_weq _ (isweq_lti_iso_to_lt_iso_from_polarized _ _ H).

End isos_facts.
