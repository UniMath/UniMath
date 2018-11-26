(** * Functor category as a displayed category
*)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Local Open Scope mor_disp_scope.


Section FunctorsDisplayed.

Context (C D:category).

(** ** Base category.

The base category contains:
- Objects: functions F₀ : C₀ → D₀
- Morphisms: transformations γₓ : D₀ ⟦F₀ x, G₀ x⟧
*)
Definition base_cat : category.
Proof.
  use makecategory.
  - exact (C → D).
  - intros F₀ G₀.
    exact (∏ (x : C), F₀ x --> G₀ x).
  - intros F₀ G₀. cbn. apply (impred 2).
    intros ?. apply D.
  - intros F₀ x. apply identity.
  - intros F₀ G₀ H₀ FG GH x.
    refine (_ · _).
    + apply FG.
    + apply GH.
  - intros F₀ G₀. cbn. intros γ.
    apply funextsec. intros x.
    apply id_left.
  - intros F₀ G₀. cbn. intros γ.
    apply funextsec. intros x.
    apply id_right.
  - intros F₀ G₀ H₀ K₀. cbn. intros γ θ μ.
    apply funextsec. intros x.
    apply assoc.
  - intros F₀ G₀ H₀ K₀. cbn. intros γ θ μ.
    apply funextsec. intros x.
    apply assoc'.
Defined.

(** ** Step 1

- Objects: actions of functors on maps
- Morphisms: naturality of transformations
  The univalence of this displayed category can be expressed as a concrete case of the Structure Identity Principle.
*)

Definition step1_disp : disp_cat base_cat.
Proof.
  use disp_struct.
  - intros F₀. exact (∏ {a b : C}, C ⟦a, b⟧ → D ⟦F₀ a, F₀ b⟧).
  - cbn. intros F₀ G₀ F₁ G₁ γ.
    exact (∏ (a b : C) (f : C ⟦a, b⟧),
           F₁ _ _ f · γ b = γ a · G₁ _ _ f).
  - intros F₀ G₀ F₁ G₁ γ. simpl.
    repeat (apply impred; intro).
    apply homset_property.
  - cbn; intros.
    etrans. apply id_right.
    apply pathsinv0. apply id_left.
  - cbn. intros ???????? S1 S2 a b f.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, S1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition, S2.
    apply assoc.
Defined.

Lemma step1_disp_univalent : is_univalent_disp step1_disp.
Proof.
  apply is_univalent_disp_from_SIP_data.
  - intros F₀. repeat (apply (impred 2); intro).
    apply homset_property.
  - intros F₀ F₁ F'₁ γ γ'.
    apply funextsec. intros a.
    apply funextsec. intros b.
    apply funextsec. intros f.
    etrans. apply pathsinv0. apply id_right.
    etrans. apply γ.
    apply id_left.
Defined.

Definition step1_total : category
  := total_category step1_disp.

(** ** Step 2

- Objects: functors preserver identities
- Morphisms: unit
*)

Definition step2_disp : disp_cat step1_total :=
  disp_full_sub step1_total
  (λ F : step1_total,
    let F₁ := pr2 F in
    ∏ (x : C), F₁ _ _ (identity x) = identity _).

(** ** Step 3

- Objects: functors preserver composition
- Morphisms: unit
*)

Definition step3_disp : disp_cat step1_total :=
  disp_full_sub step1_total
  (λ F : step1_total,
    let F₁ := pr2 F in
    ∏ (a b c: C) (f : C⟦a,b⟧) (g : C⟦b,c⟧),
    F₁ _ _ (f · g) = F₁ _ _ f · F₁ _ _ g).

(** ** Step 4
    Combine everything together
*)

Definition functor_disp_cat : disp_cat step1_total
  := dirprod_disp_cat step2_disp step3_disp.

Definition functor_total_cat : category
  := total_category functor_disp_cat.

(* TODO: This is equivalent to the direct construction. *)
(* Lemma functor_total_cat_correct : *)
(*   functor_total_cat = functor_category C D. *)
(* Proof. *)
(*   apply subtypeEquality. *)
(*   { intro. apply isaprop_has_homsets. } *)

Lemma functor_disp_cat_univalent :
  is_univalent_disp functor_disp_cat.
Proof.
  apply dirprod_disp_cat_is_univalent.
  - apply disp_full_sub_univalent.
    intros [F₀ F₁]. apply impred. intros x.
    cbn[pr2].
    apply homset_property.
  - apply disp_full_sub_univalent.
    intros [F₀ F₁].
    repeat (apply impred; intros ?).
    cbn[pr2].
    apply homset_property.
Defined.

Definition base_cat_iso_to_iso_fam (F₀ G₀ : base_cat) :
  iso F₀ G₀ → (∏ (x : C), iso (F₀ x) (G₀ x)).
Proof.
  intros [γ Hγ].
  apply is_z_iso_from_is_iso in Hγ.
  destruct Hγ as [θ [Hγθ Hθγ]].
  intros x. apply z_iso_to_iso.
  exists (γ x), (θ x). split.
  - apply (toforallpaths _ _ _ Hγθ).
  - apply (toforallpaths _ _ _ Hθγ).
Defined.

Definition base_cat_iso_fam_to_iso (F₀ G₀ : base_cat) :
  (∏ (x : C), iso (F₀ x) (G₀ x)) → iso F₀ G₀.
Proof.
  intros γ.
  apply z_iso_to_iso.
  exists γ, (λ x, inv_from_iso (γ x)).
  split.
  - apply funextsec. intros x. cbn.
    apply iso_inv_after_iso.
  - apply funextsec. intros x. cbn.
    apply iso_after_iso_inv.
Defined.

Lemma base_cat_iso_weq (F₀ G₀ : base_cat) :
  iso F₀ G₀ ≃ (∏ (x : C), iso (F₀ x) (G₀ x)).
Proof.
  exists (base_cat_iso_to_iso_fam F₀ G₀).
  use gradth.
  - apply base_cat_iso_fam_to_iso.
  - intros x. apply eq_iso. reflexivity.
  - intros x. apply funextsec. intros y.
    apply eq_iso. reflexivity.
Defined.

Definition base_cat_iso_fam_weq (F₀ G₀ : base_cat) :
  is_univalent D →
  F₀ ~ G₀ ≃ (∏ (x : C), iso (F₀ x) (G₀ x)).
Proof.
  intros HD.
  apply weqonsecfibers. intros x.
  exists idtoiso. apply HD.
Defined.

Definition base_cat_iso_weq_aux
      (F₀ G₀ : base_cat) :
  is_univalent D →
  F₀ = G₀ ≃ iso F₀ G₀.
Proof.
  intros HD.
  eapply weqcomp. apply weqtoforallpaths.
  eapply weqcomp. apply base_cat_iso_fam_weq, HD.
  apply invweq. apply base_cat_iso_weq.
Defined.

Lemma base_cat_univalent :
  is_univalent D →
  is_univalent base_cat.
Proof.
  intros HD.
  unfold is_univalent. split; [ | apply base_cat ].
  unfold base_cat. simpl.
  intros F₀ G₀.
  use isweqhomot.
  - apply base_cat_iso_weq_aux, HD.
  - intros p. induction p. simpl.
    apply eq_iso. reflexivity.
  - apply base_cat_iso_weq_aux.
Defined.

Lemma functor_total_cat_univalent :
  is_univalent D →
  is_univalent functor_total_cat.
Proof.
  intros HD.
  apply is_univalent_total_category.
  - apply is_univalent_total_category.
    + apply base_cat_univalent, HD.
    + apply step1_disp_univalent.
  - apply functor_disp_cat_univalent.
Defined.

End FunctorsDisplayed.
