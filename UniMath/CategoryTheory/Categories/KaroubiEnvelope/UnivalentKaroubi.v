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

Require Import UniMath.CategoryTheory.Retracts.

Local Open Scope cat.

Let P (X : category) : univalent_category.
Proof.
  use make_univalent_category.
  - exact ([X^op, SET]).
  - apply is_univalent_functor_category.
    apply is_univalent_HSET.
Defined.

Let y (X : category) : functor X (P X)
    := yoneda X.

Section RetractsOfPresheaves.

  Context {X : category}.

  Definition presheaf_is_retract (F : P X) : UU
    := ∥ ∑ x : X, retraction F (y X x) ∥.

  Lemma isaprop_presheaf_is_retract (F : P X)
    : isaprop (presheaf_is_retract F).
  Proof.
    apply isapropishinh.
  Qed.

  Lemma representable_presheaf_is_retract
    : ∏ x : X, presheaf_is_retract (y X x).
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
    - exact (P X).
    - exact (λ F, presheaf_is_retract F).
  Defined.

  Lemma is_univalent_karoubi_envelope
    : is_univalent univ_karoubi_envelope.
  Proof.
    apply is_univalent_full_subcat.
    - apply (P X).
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
      exists (y X x).
      apply representable_presheaf_is_retract.
    - intros x₀ x₁ f.
      exact (#(y X) f ,, tt).
  Defined.

  Lemma embedding_into_karoubi_envelope_is_functor
    : is_functor embedding_into_karoubi_envelope_data.
  Proof.
    split ; intro ; intros
    ; apply univ_karoubi_envelope_eq_on_mor ; apply (y X).
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
    : (#(y X) g = pr1 f) ≃ #(y X) g ,, tt = f.
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
    - exact (∑ g : X ⟦x₁, x₂⟧, #(y X) g = pr1 f).
    - unfold hfiber.
      use weqfibtototal.
      intro.
      apply univ_karoubi_envelope_eq_on_mor_from_embedding.
    - exact (yoneda_fully_faithful X x₁ x₂ (pr1 f)).
  Defined.

End EmbeddingIntoKaroubiEnvelope.
