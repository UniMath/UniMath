(**************************************************************************************************

  The Univalent Karoubi Envelope

  The univalent Karoubi envelope (or cauchy completion) of a category C,
  is the full subcategory of presheaves on C classified by the predicate:
  A presheaf P is a retract of X(-, x), for some x : ob X.

  Contents
  1. The univalent Karoubi envelope
  1.1. The category [univalent_karoubi_cat]
  1.2. The fully faithful embedding [embedding_into_karoubi]
  1.3. Every idempotent in the karoubi envelope splits [univalent_karoubi_idempotents_split]
  1.4. Every object of the karoubi envelope is a retract of an element of C
    [univalent_karoubi_objects_are_retracts]
  1.5. The bundling of the above into a term of univalent_karoubi_envelope [univalent_karoubi]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Retracts.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.Core.

Local Open Scope cat.

(** * 1. The univalent Karoubi envelope *)
(** ** 1.1. The category *)
Section RetractsOfPresheaves.

  Context {X : category}.

  Definition presheaf_is_retract (F : [X^op, SET]) : UU
    := ∃ (x : X), retraction F (yoneda X x).

  Lemma isaprop_presheaf_is_retract (F : [X^op, SET])
    : isaprop (presheaf_is_retract F).
  Proof.
    apply isapropishinh.
  Qed.

  Lemma representable_presheaf_is_retract
    : ∏ x : X, presheaf_is_retract (yoneda X x).
  Proof.
    intro x.
    apply hinhpr.
    exists x.
    use make_retraction.
    - apply identity.
    - apply identity.
    - apply id_left.
  Qed.

End RetractsOfPresheaves.

Section DefinitionOfKaroubi.

  Context (X : category).

  Definition univalent_karoubi_cat
    : category
    := full_subcat [X^op, SET] presheaf_is_retract.

  Lemma is_univalent_karoubi_cat
    : is_univalent univalent_karoubi_cat.
  Proof.
    apply is_univalent_full_subcat.
    - apply is_univalent_functor_category, is_univalent_HSET.
    - intro ; apply isaprop_presheaf_is_retract.
  Qed.

End DefinitionOfKaroubi.

Section HelperLemmas.

  Lemma univalent_karoubi_eq_on_mor
    {X : category} {o₁ o₂ : univalent_karoubi_cat X} (f g : _⟦o₁, o₂⟧)
    : pr1 f = pr1 g → f = g.
  Proof.
    intro p.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    exact p.
  Qed.

End HelperLemmas.

(** ** 1.2. The fully faithful embedding *)
Section EmbeddingIntoKaroubi.

  Context (X : category).

  Let KE : category := univalent_karoubi_cat X.

  Definition embedding_into_karoubi_data
    : functor_data X KE.
  Proof.
    use make_functor_data.
    - intro x.
      exists (yoneda X x).
      apply representable_presheaf_is_retract.
    - intros x₀ x₁ f.
      exact (#(yoneda X) f ,, tt).
  Defined.

  Lemma embedding_into_karoubi_is_functor
    : is_functor embedding_into_karoubi_data.
  Proof.
    split ; intro ; intros
    ; apply univalent_karoubi_eq_on_mor ; apply (yoneda X).
  Qed.

  Definition embedding_into_karoubi
    : X ⟶ KE.
  Proof.
    use make_functor.
    - exact embedding_into_karoubi_data.
    - apply embedding_into_karoubi_is_functor.
  Defined.

  Local Lemma univalent_karoubi_eq_on_mor_from_embedding
    {x₁ x₂ : X}
    (f : KE⟦embedding_into_karoubi x₁, embedding_into_karoubi x₂⟧)
    (g : X ⟦x₁, x₂⟧)
    : (#(yoneda X) g = pr1 f) ≃ #(yoneda X) g ,, tt = f.
  Proof.
    use weq_iso.
    - intro p.
      apply (univalent_karoubi_eq_on_mor (#embedding_into_karoubi g) f).
      exact p.
    - intro p.
      induction p.
      apply idpath.
    - intro ; apply homset_property.
    - intro.
      use proofirrelevance.
      apply (homset_property KE (embedding_into_karoubi _) (embedding_into_karoubi _)).
  Qed.

  Corollary embedding_into_karoubi_is_fully_faithful
    : fully_faithful embedding_into_karoubi.
  Proof.
    intros x₁ x₂.
    intro f.
    use iscontrweqf.
    - exact (∑ g : X ⟦x₁, x₂⟧, #(yoneda X) g = pr1 f).
    - unfold hfiber.
      use weqfibtototal.
      intro.
      apply univalent_karoubi_eq_on_mor_from_embedding.
    - exact (yoneda_fully_faithful X x₁ x₂ (pr1 f)).
  Defined.

End EmbeddingIntoKaroubi.

(** ** 1.3. Every idempotent in the karoubi envelope splits *)
Section SplitIdempotents.

  Context {C : category}.
  Context (X : univalent_karoubi_cat C).
  Context (f : idempotent X).

  Definition univalent_karoubi_split_idempotent_presheaf
    : PreShv C
    := Equalizers_PreShv _ _ (identity _) (pr1 (idempotent_morphism f)).

  Definition univalent_karoubi_split_idempotent_presheaf_retraction
    : retraction univalent_karoubi_split_idempotent_presheaf (pr1 X).
  Proof.
    use make_retraction.
    - apply EqualizerArrow.
    - refine (EqualizerIn _ _ (pr1 (idempotent_morphism f)) _).
      refine (id_right _ @ !base_paths _ _ (idempotent_is_idempotent f)).
    - abstract (
        apply EqualizerInsEq;
        refine (assoc' _ _ _ @ _);
        refine (maponpaths _ (EqualizerCommutes _ _ _ _) @ _);
        refine (_ @ !id_left _);
        refine (_ @ id_right _);
        exact (!EqualizerEqAr _)
      ).
  Defined.

  Definition univalent_karoubi_split_idempotent_object
    : univalent_karoubi_cat C.
  Proof.
    exists univalent_karoubi_split_idempotent_presheaf.
    refine (hinhfun _ (pr2 X)).
    intro HX.
    exists (pr1 HX).
    exact (compose_retraction
      univalent_karoubi_split_idempotent_presheaf_retraction
      (pr2 HX)).
  Defined.

  Definition univalent_karoubi_split_idempotent
    : is_split_idempotent f.
  Proof.
    use make_is_split_idempotent.
    - exact univalent_karoubi_split_idempotent_object.
    - apply (fully_faithful_functor_reflects_retraction _ (full_subcat_pr1_fully_faithful _ _)).
      exact univalent_karoubi_split_idempotent_presheaf_retraction.
    - abstract (
        apply univalent_karoubi_eq_on_mor;
        exact (!EqualizerCommutes _ _ _ _)
      ).
  Defined.

End SplitIdempotents.

Definition univalent_karoubi_idempotents_split
  (C : category)
  : idempotents_split (univalent_karoubi_cat C).
Proof.
  intros X f.
  apply hinhpr.
  apply univalent_karoubi_split_idempotent.
Defined.

(** ** 1.4. Every object of the karoubi envelope is a retract of an element of C *)
Definition univalent_karoubi_objects_are_retracts
  (C : category)
  : objects_are_retracts (embedding_into_karoubi C).
Proof.
  intro X.
  refine (hinhfun _ (pr2 X)).
  intro HX.
  exists (pr1 HX).
  apply (fully_faithful_functor_reflects_retraction _ (full_subcat_pr1_fully_faithful _ _)).
  exact (pr2 HX).
Defined.

(** ** 1.5. The bundling of the above into a term of univalent_karoubi_envelope *)
Definition univalent_karoubi
  (C : category)
  : univalent_karoubi_envelope C.
Proof.
  use make_univalent_karoubi_envelope.
  - use make_karoubi_envelope.
    + use make_karoubi_envelope_data.
      * exact (univalent_karoubi_cat C).
      * exact (embedding_into_karoubi C).
    + apply make_is_karoubi_envelope.
      * exact (univalent_karoubi_idempotents_split C).
      * exact (embedding_into_karoubi_is_fully_faithful C).
      * exact (univalent_karoubi_objects_are_retracts C).
  - apply (is_univalent_karoubi_cat C).
Defined.
