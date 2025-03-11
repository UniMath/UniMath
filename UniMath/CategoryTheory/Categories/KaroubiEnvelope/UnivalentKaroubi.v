(* The Karoubi Envelope of a category C, also referred to as the cauchy completion of C,
   is the full subcategory of presheaves on C classified by the predicate:
   A presheaf P is a retract of X(-,x), for some x : ob X.

   1. Definition
   2. Universal property.
   2.1. Embedding: functor + ff
   2.2. Splitting [TODO]

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.

Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Set.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.FunctorCategory.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Fullsub.

Local Open Scope cat.

Section RetractsOfPresheaves.

  Context {X : category}.

  Definition presheaf_is_retract (F : [X^op, SET]) : UU
    := ∥ ∑ x : X, retraction F (yoneda X x) ∥.

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
    simple refine (_ ,, _ ,, _).
    - apply identity.
    - apply identity.
    - apply id_left.
  Qed.

End RetractsOfPresheaves.

Section DefinitionOfKaroubiEnvelope.

  Context (X : category).

  Definition univ_karoubi_envelope : category.
  Proof.
    use full_subcat.
    - exact ([X^op, SET]).
    - exact (λ F, presheaf_is_retract F).
  Defined.

  Lemma is_univalent_karoubi_envelope
    : is_univalent univ_karoubi_envelope.
  Proof.
    apply is_univalent_full_subcat.
    - apply is_univalent_functor_category, is_univalent_HSET.
    - intro ; apply isaprop_presheaf_is_retract.
  Qed.

  Definition univalent_karoubi_envelope : univalent_category
    := _ ,, is_univalent_karoubi_envelope.

End DefinitionOfKaroubiEnvelope.

Section HelperLemmas.

  Lemma univ_karoubi_envelope_eq_on_mor
    {X : category} {o₁ o₂ : univ_karoubi_envelope X} (f g : _⟦o₁, o₂⟧)
    : pr1 f = pr1 g → f = g.
  Proof.
    intro p.
    use total2_paths2.
    - exact p.
    - use proofirrelevance.
      use isapropifcontr.
      apply iscontrunit.
  Qed.

End HelperLemmas.

Section EmbeddingIntoKaroubiEnvelope.

  Context (X : category).

  Let KE : univalent_category := univalent_karoubi_envelope X.

  Definition embedding_into_karoubi_envelope_data
    : functor_data X KE.
  Proof.
    use make_functor_data.
    - intro x.
      exists (yoneda X x).
      apply representable_presheaf_is_retract.
    - intros x₀ x₁ f.
      exact (#(yoneda X) f ,, tt).
  Defined.

  Lemma embedding_into_karoubi_envelope_is_functor
    : is_functor embedding_into_karoubi_envelope_data.
  Proof.
    split ; intro ; intros
    ; apply univ_karoubi_envelope_eq_on_mor ; apply (yoneda X).
  Qed.

  Definition embedding_into_karoubi_envelope
    : functor X KE.
  Proof.
    use make_functor.
    - exact embedding_into_karoubi_envelope_data.
    - apply embedding_into_karoubi_envelope_is_functor.
  Defined.

  Local Lemma univ_karoubi_envelope_eq_on_mor_from_embedding
    {x₁ x₂ : X}
    (f : KE⟦embedding_into_karoubi_envelope x₁, embedding_into_karoubi_envelope x₂⟧)
    (g : X ⟦x₁, x₂⟧)
    : (#(yoneda X) g = pr1 f) ≃ #(yoneda X) g ,, tt = f.
  Proof.
    use weq_iso.
    - intro p.
      apply (univ_karoubi_envelope_eq_on_mor (#embedding_into_karoubi_envelope g) f).
      exact p.
    - intro p.
      induction p.
      apply idpath.
    - intro ; apply homset_property.
    - intro.
      use proofirrelevance.
      apply (homset_property KE (embedding_into_karoubi_envelope _) (embedding_into_karoubi_envelope _)).
  Qed.

  Corollary embedding_into_karoubi_envelope_is_fully_faithful
    : fully_faithful embedding_into_karoubi_envelope.
  Proof.
    intros x₁ x₂.
    intro f.
    use iscontrweqf.
    - exact (∑ g : X ⟦x₁, x₂⟧, #(yoneda X) g = pr1 f).
    - unfold hfiber.
      use weqfibtototal.
      intro.
      apply univ_karoubi_envelope_eq_on_mor_from_embedding.
    - exact (yoneda_fully_faithful X x₁ x₂ (pr1 f)).
  Defined.

End EmbeddingIntoKaroubiEnvelope.

Lemma composite_of_retractions {C : category} {x y z : C}
  (r : retraction x y) (s : retraction y z)
  : retraction x z.
Proof.
  exists (retraction_section r · retraction_section s).
  exists (retraction_retraction s · retraction_retraction r).
  unfold is_retraction.
  refine (assoc _ _ _ @ _).
  etrans. {
    apply maponpaths_2.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    exact (retraction_is_retraction s).
  }
  etrans. {
    apply maponpaths_2.
    apply id_right.
  }
  apply retraction_is_retraction.
Qed.

Proposition idempotents_in_karoubi_envelope_split (X : category)
    : idempotents_split (univ_karoubi_envelope X).
Proof.
  use idempotents_split_in_full_subcat.
  - apply idempotents_split_in_functor_cat.
    + apply is_univalent_HSET.
    + apply idempotents_split_in_set.
  - intros F G r.
    use (factor_through_squash _ _ (pr2 F)).
    { apply isapropishinh. }
    intros [x r'].
    apply hinhpr.
    exists x.
    exact (composite_of_retractions r r').
Defined.
