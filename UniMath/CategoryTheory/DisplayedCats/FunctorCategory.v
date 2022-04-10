(** * Functor category as a displayed category
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition base_precategory_ob_mor (C D:precategory_data)
  : precategory_ob_mor
  := make_precategory_ob_mor (C → D)
                             (λ F₀ G₀ : C → D, ∏ x : C, D ⟦ F₀ x, G₀ x ⟧).

Definition base_precategory_data (C D:precategory_data) : precategory_data
  := make_precategory_data
       (base_precategory_ob_mor C D)
       (λ (F₀ : C → D) (x : C), identity (F₀ x))
       (λ (F₀ G₀ H₀ : C → D)
          (FG : ∏ x : C, D ⟦ F₀ x, G₀ x ⟧)
          (GH : ∏ x : C, D ⟦ G₀ x, H₀ x ⟧)
          (x : C),
        FG x · GH x).

Section FunctorsDisplayed.

Context (C D : category).

(** ** Base category.

The base category contains:
- Objects: functions F₀ : C₀ → D₀
- Morphisms: transformations γₓ : D₀ ⟦F₀ x, G₀ x⟧
 *)

Lemma is_precategory_base_precategory_data
  : is_precategory (base_precategory_data C D).
Proof.
  apply make_is_precategory.
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
Qed.

Definition base_precategory
  : precategory
  := make_precategory (base_precategory_data C D)
                      is_precategory_base_precategory_data.

Lemma has_homsets_base_precategory_ob_mor
  : has_homsets (base_precategory_ob_mor C D).
Proof.
  intros F₀ G₀. cbn. apply (impred 2). intro. apply D.
Qed.

Definition base_category
  : category
  := make_category base_precategory
                   has_homsets_base_precategory_ob_mor.

(** ** Step 1

- Objects: actions of functors on maps
- Morphisms: naturality of transformations

  The univalence of this displayed category can be expressed as a
  concrete case of the Structure Identity Principle (however,
  UniMath.CategoryTheory.DisplayedCats.SIP is not employed).
*)

Definition disp_morph : disp_cat_data (base_precategory_data C D).
Proof.
  use tpair.
  - exists (λ F₀, ∏ (a b : C), C ⟦a, b⟧ → D ⟦F₀ a, F₀ b⟧).
    cbn. intros F₀ G₀ F₁ G₁ γ.
    exact (∏ (a b : C) (f : C ⟦a, b⟧), F₁ _ _ f · γ b = γ a · G₁ _ _ f).
  - repeat use tpair; cbn.
    + cbn; intros.
      etrans. apply id_right.
      apply pathsinv0. apply id_left.
    + cbn. intros ???????? S1 S2 a b f.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition, S1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition, S2.
      apply assoc.
Defined.

Lemma step1_disp_axioms
  : disp_cat_axioms base_category disp_morph.
Proof.
  repeat split; intros; repeat (apply impred; intro);
    repeat (apply funextsec; intro); try apply homset_property.
  cbn.
  repeat (apply (impred 2); intro).
  apply hlevelntosn.
  apply homset_property.
Qed.

Definition step1_disp : disp_cat base_category.
Proof.
  exists disp_morph.
  exact step1_disp_axioms.
Defined.

Lemma step1_disp_univalent : is_univalent_disp step1_disp.
Proof.
  apply is_univalent_disp_from_fibers.
  hnf; cbn; intros x f g.
  apply isweqimplimpl.
  - intro i.
    unfold iso_disp in i.
    cbn in i.
    apply funextsec. intro.
    destruct i as (ff, Hff).
    apply funextsec. intro.
    apply funextsec. intro.
    etrans.
    { apply pathsinv0. apply id_right. }
    etrans.
    { apply ff. }
    apply id_left.
  - assert (KK : isaset (∏ a b : C, C ⟦ a, b ⟧ → D ⟦ x a, x b ⟧)).
    + repeat (apply (impred 2); intro).
      apply homset_property.
    + apply KK.
  - apply isaproptotal2.
    + unfold isPredicate.
      intro u.
      apply (isaprop_is_iso_disp (D := step1_disp)).
    + cbn.
      intros u v Hu Hv.
      apply funextsec. intro a.
      apply funextsec. intro b.
      apply funextsec. intro t.
      apply homset_property.
Defined.

Definition step1_total : category
  := total_category step1_disp.

(** ** Step 2

- Objects: functors preserve identities
- Morphisms: unit
*)

Definition step2_disp : disp_cat step1_total :=
  disp_full_sub step1_total
  (λ F : step1_total,
    let F₁ := pr2 F in
    ∏ (x : C), F₁ _ _ (identity x) = identity _).

(** ** Step 3

- Objects: functors preserve composition
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

(** This construction is univalent *)
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

Definition base_category_iso_to_iso_fam (F₀ G₀ : base_category) :
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

Definition base_category_iso_fam_to_iso (F₀ G₀ : base_category) :
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

Lemma base_category_iso_weq (F₀ G₀ : base_category) :
  iso F₀ G₀ ≃ (∏ (x : C), iso (F₀ x) (G₀ x)).
Proof.
  exists (base_category_iso_to_iso_fam F₀ G₀).
  use gradth.
  - apply base_category_iso_fam_to_iso.
  - intros x. apply eq_iso. apply idpath.
  - intros x. apply funextsec. intros y.
    apply eq_iso. apply idpath.
Defined.

Definition base_category_iso_fam_weq (F₀ G₀ : base_category) :
  is_univalent D →
  F₀ ~ G₀ ≃ (∏ (x : C), iso (F₀ x) (G₀ x)).
Proof.
  intros HD.
  apply weqonsecfibers. intros x.
  exists idtoiso. apply HD.
Defined.

Definition base_category_iso_weq_aux
      (F₀ G₀ : base_category) :
  is_univalent D →
  F₀ = G₀ ≃ iso F₀ G₀.
Proof.
  intros HD.
  eapply weqcomp. apply weqtoforallpaths.
  eapply weqcomp. apply base_category_iso_fam_weq, HD.
  apply invweq. apply base_category_iso_weq.
Defined.

Lemma base_category_univalent
  : is_univalent D → is_univalent base_category.
Proof.
  intros HD.
  unfold is_univalent.
  unfold base_category. simpl.
  intros F₀ G₀.
  use isweqhomot.
  - apply base_category_iso_weq_aux, HD.
  - intros p. induction p. simpl.
    apply eq_iso. apply idpath.
  - apply base_category_iso_weq_aux.
Defined.

Lemma functor_total_cat_univalent
  : is_univalent D → is_univalent functor_total_cat.
Proof.
  intros HD.
  apply is_univalent_total_category.
  - apply is_univalent_total_category.
    + apply base_category_univalent, HD.
    + apply step1_disp_univalent.
  - apply functor_disp_cat_univalent.
Defined.

End FunctorsDisplayed.
