(* The Karoubi Envelope of a category C, also referred to as the cauchy completion of C,
   is the full subcategory of presheaves on C classified by the predicate:
   A presheaf P is a retract of X(-,x), for some x : ob X.

   1. Definition
   2. Universal property.
   2.1. Embedding: functor + ff
   2.2. Splitting

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

Definition idempotents_split
    (D : category)
    : UU
  := ∏ (X : D) (f : idempotent X), ∥ is_split_idempotent f ∥.

Section IdempotentsSplitInSet.

  (* Fix f idempotent *)
  Context {A : SET} {f : SET⟦A, A⟧} (p : f · f = f).

  (* Let I : UU := ∑ b : pr1 A, ∃ a : pr1 A, f a = b.*)
  Let I : UU := ∑ b : pr1 A, f b = b.
  Let J : SET.
  Proof.
    exists I.
    apply isaset_total2.
    - apply A.
    - intro.
      apply isasetaprop.
      apply A.
  Defined.

  Let pr : SET⟦A, J⟧.
  Proof.
    intro a.
    exists (f a).
    exact ((toforallpaths _ _ _ p) a).
  Defined.

  Let inc : SET⟦J, A⟧ := pr1.

  Lemma image_fact_gives_retraction
    : is_retraction inc pr.
  Proof.
    apply funextsec.
    intro i.
    use subtypePath. {
      intro ; apply A.
    }
    exact (pr2 i).
  Defined.

  Definition splitting_in_set : is_split_idempotent f.
  Proof.
    exists J.
    simple refine ((inc ,, pr ,, _) ,, _).
    - exact image_fact_gives_retraction.
    - apply funextsec ; intro ; apply idpath.
  Defined.

End IdempotentsSplitInSet.

Proposition idempotents_split_in_set
  : idempotents_split SET.
Proof.
  intro ; intro.
  apply hinhpr.
  apply splitting_in_set.
  apply f.
Defined.

Section UniquenessOfSplitIdempotents.

  Context {C : category} {x : C} (f : C⟦x, x⟧) (C_is_univ : is_univalent C).

  Lemma isaprop_is_split_idempotent : isaprop (is_split_idempotent f).
  Proof.
  (* Assume f : x → x split as x →r y →s x and x →R Y →S x
     Claim: y ≅ Y
     r · s = id_x
   *)
    intros [a [[proj inj] pf]] [A [[Proj Inj] Pf]].
    simpl in *.


  Admitted.

End UniquenessOfSplitIdempotents.

(* Lemma isaprop_is_split_idempotent
  {C : category} {x : C} (f : C⟦x, x⟧) (C_is_univ : is_univalent C)
  : isaprop (is_split_idempotent f).
Proof.
Admitted. *)

Section IdempotentsSplitInFunctorCats.

  Context {C D : category} (Du : is_univalent D) (Ds : idempotents_split D).

  Definition type_of_choice
    {F : [C, D]} (α : _⟦F, F⟧)
    {c : C} (p : pr1 α c · pr1 α c = pr1 α c)
      : UU
    := ∑ (d : D) (H : retraction d (pr1 F c)),
      pr1 α c = H · retraction_section H.

  Lemma isaprop_type_of_choice
    {F : [C, D]} (α : _⟦F, F⟧)
    {c : C} (p : pr1 α c · pr1 α c = pr1 α c)
    : isaprop (type_of_choice α p).
  Proof.
    apply isaprop_is_split_idempotent.
    apply Du.
  Qed.

  Context {F : [C, D]}
    {α : [C, D]⟦F, F⟧}
    (s : is_idempotent α).

  Lemma create_split_idempotent_functor_ob
    : ∏ c : C, type_of_choice α (toforallpaths _ _ _ (base_paths _ _ s) c).
  Proof.
    intro c.
    set (t := toforallpaths _ _ _ (base_paths _ _ s) c).
    set (q := Ds (pr1 F c) (pr1 α c ,, t)).
    exact (factor_through_squash (isaprop_type_of_choice α t) (idfun _) q).
  Defined.

  Definition create_split_idempotent_functor_data
    : functor_data C D.
  Proof.
    use make_functor_data.
    - exact (λ c, pr1 (create_split_idempotent_functor_ob c)).
    - intros c1 c2 f.
      set (d1 := create_split_idempotent_functor_ob c1).
      set (d2 := create_split_idempotent_functor_ob c2).
      exact (pr112 d1 · #(pr1 F) f · pr1 (pr212 d2)).
  Defined.

  Lemma create_split_idempotent_functor_laws
    : is_functor create_split_idempotent_functor_data.
  Proof.
    split.
    - intro.
      cbn.
      rewrite (functor_id F).
      rewrite id_right.
      set (d := create_split_idempotent_functor_ob a).
      exact (pr2 (pr212 d)).
    - intro ; intros.
      cbn.
      (* rewrite (functor_comp F).
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.

      etrans.
      2: {
        apply maponpaths.
      set (d := create_split_idempotent_functor_ob s b).
      set (e := pr2 (pr212 d)).
      cbn in e.
      unfold is_retraction in e. *)
      admit.
  Admitted.

  Lemma create_split_idempotent
    : [C, D].
  Proof.
    use make_functor.
    - exact create_split_idempotent_functor_data.
    - apply create_split_idempotent_functor_laws.
  Defined.

  Lemma TODO (A : UU) : A. Proof. Admitted.

  Definition create_split_idempotent_retraction
    : create_split_idempotent_functor_data ⟹ pr1 F.
  Proof.
    use make_nat_trans.
    - exact (λ c, pr112 (create_split_idempotent_functor_ob c)).
    - intros c1 c2 f.
      cbn.
      rewrite assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      set (d := create_split_idempotent_functor_ob c2).
      apply TODO.
  Defined.

  Definition create_split_idempotent_section
    : pr1 F ⟹ create_split_idempotent_functor_data.
  Proof.
    use make_nat_trans.
    - exact (λ c, pr1 (pr212 (create_split_idempotent_functor_ob c))).
    - intros c1 c2 f.
      cbn.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply TODO.
  Defined.

  Definition create_split_idempotent_retract
    : retraction create_split_idempotent F.
  Proof.
    simple refine (_ ,, _ ,, _) ; simpl.
    - exact create_split_idempotent_retraction.
    - exact create_split_idempotent_section.
    - use nat_trans_eq.
      { apply homset_property. }
      exact (λ c, pr2 (pr212 (create_split_idempotent_functor_ob c))).
  Defined.

End IdempotentsSplitInFunctorCats.

Lemma idempotents_split_in_functor_cat
  {C D : category} (Du : is_univalent D) (Ds : idempotents_split D)
  : idempotents_split [C, D].
Proof.
  unfold idempotents_split.
  intros F [α s].
  apply hinhpr.
  simple refine (_ ,, _ ,, _).
  - exact (create_split_idempotent Du Ds s).
  - exact (create_split_idempotent_retract Du Ds s).
  - use nat_trans_eq.
    { apply homset_property. }
    intro c.
    exact (pr22 (create_split_idempotent_functor_ob Du Ds s c)).
Defined.

Section IdempotentsSplitInFullSubCats.

  Context {X : category} (P : X → hProp)
    (Xs : idempotents_split X).

  Lemma split_in_fullsub_to_base {x : full_subcat X (λ x : X, P x)}
    {e : X⟦pr1 x, pr1 x⟧}
    {g : is_idempotent e}
    (ei : is_split_idempotent e)
    : is_split_idempotent (C := full_subcat _ _) (e ,, tt)
      → is_split_idempotent e.
  Proof.
    intro s.
    induction s as [[y ?] [[[r ?] [[s ?] ss]] p]].
    cbn in *.
    exists y.
    simple refine ((_ ,, (_,,_)) ,, _).
    - exact r.
    - exact s.
    - exact (base_paths _ _ ss).
    - exact (base_paths _ _ p).
  Defined.

  Proposition idempotents_split_in_full_subcat
    : idempotents_split (full_subcat _ P).
  Proof.
    intros x f.
    use (factor_through_squash _ _ (Xs (pr1 x) (pr11 f ,, base_paths _ _ (pr2 f)))).
    - apply isapropishinh.
    - intro ei.
      apply hinhpr.
      (* apply (split_in_fullsub_to_base ei). *)
      admit.
  Admitted.

End IdempotentsSplitInFullSubCats.

Proposition idempotents_in_karoubi_envelope_split (X : category)
    : idempotents_split (univ_karoubi_envelope X).
Proof.
  use idempotents_split_in_full_subcat.
  apply idempotents_split_in_functor_cat.
  - apply is_univalent_HSET.
  - apply idempotents_split_in_set.
Qed.
