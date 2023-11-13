(********************************************************************************

 Precomposition is fully faithful

 To prove the universal property of the Rezk completion of enriched categories,
 we need to prove that precomposition with a weak equivalence gives rise to an
 adjoint equivalence between functor categories to univalent categories. To prove
 this statement, we show that this precomposition functor is both fully faithful
 and essentially surjective. In this file, we prove that it is fully faithful.

 More specifically, we are interested in the following statement:
 Let `F : C₁ ⟶ C₂` be a fully faithful and essentially surjective enriched
 functor. The functor from enriched functor category `C₂ ⟶ C₃` to the enriched
 functor category `C₁ ⟶ C₃` given by precomposition with `F`, is fully faithful.

 The proof of this statement is similar to how the universal property of the Rezk
 completion is proven for ordinary categories. The main idea in this proof is as
 follows. At several points, we need that `F` is essentially surjective. This is
 to find preimages of objects in `C₂` along `F`. However, we can only get such
 preimages if we are proving a proposition, because essential surjective only
 gives the mere existence of preimages. To guarantee that we are proving a
 proposition, we formulate our statements using contractibility.

 For example, to prove fullness, we need to show that every enriched natural
 transformation has a preimage. To define the preimage, we need to describe the
 morphisms of this transformation. If we would be looking at the type
 `G₁ x --> G₂ x`, which would be the type that we want, then we are not proving a
 proposition, so we cannot use essential surjectivity. We improve upon that in
 the statement [enriched_rezk_completion_ump_full_iscontr]. Here we are looking
 for a morphisms `G₁ x --> G₂ x` that satisfies some additional property, and
 that extra property, guarantees that we have a unique morphism. As such, the
 type becomes a proposition, and this way we are able to use essential
 surjectivity.

 All of this is the same as for ordinary categories. For enriched categories, we
 also need to prove that this transformation is enriched
 ([enriched_rezk_completion_ump_full_nat_trans_enrichment]). In essence, this
 proof follows the proof of naturality for the transformation. The key difference
 is that it is formulated in the language of enriched categories rather than that
 of ordinary categories.

 Contents
 1. Faithfulness
 2. Fullness

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.FullyFaithful.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Precomposition.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section PrecompositionFullyFaithful.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {C₃ : univalent_category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (EF : functor_enrichment F E₁ E₂)
          (HF₁ : essentially_surjective F)
          (HF₂ : fully_faithful_enriched_functor EF).

  Let F_fully_faithful : fully_faithful F
    := fully_faithful_enriched_functor_to_fully_faithful _ HF₂.

  (** * 1. Faithfulness *)
  Proposition enriched_rezk_completion_ump_faithful
    : faithful (enriched_precomp E₃ EF).
  Proof.
    intros G₁ G₂ τ.
    use invproofirrelevance.
    intros θ₁ θ₂.
    use subtypePath.
    {
      intro.
      apply (homset_property (enriched_functor_category _ _)).
    }
    use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ].
    use nat_trans_eq ; [ apply homset_property | ].
    intro y.
    assert (H := HF₁ y).
    revert H.
    use factor_through_squash.
    {
      apply homset_property.
    }
    intros x.
    induction x as [ x f ].
    refine (!(id_left _) @ _ @ id_left _).
    rewrite <- (z_iso_after_z_iso_inv (functor_on_z_iso (pr1 G₁) f)).
    rewrite !assoc'.
    apply maponpaths.
    pose (maponpaths (λ z, pr11 z x · #(pr11 G₂) f) (pr2 θ₁ @ !(pr2 θ₂))) as p.
    cbn in p.
    rewrite <- (nat_trans_ax (pr11 θ₁)) in p.
    rewrite <- (nat_trans_ax (pr11 θ₂)) in p.
    exact p.
  Qed.

  (** * 2. Fullness *)
  Section Fullness.
    Context {G₁ G₂ : C₂ ⟶ C₃}
            (τ : F ∙ G₁ ⟹ F ∙ G₂)
            {EG₁ : functor_enrichment G₁ E₂ E₃}
            {EG₂ : functor_enrichment G₂ E₂ E₃}
            (Eτ : nat_trans_enrichment
                    τ
                    (functor_comp_enrichment EF EG₁)
                    (functor_comp_enrichment EF EG₂)).

    Section OnOb.
      Context (x : C₂).

      Proposition enriched_rezk_completion_ump_full_isaprop
        : isaprop
            (∑ (f : G₁ x --> G₂ x),
             ∏ (w : C₁)
               (i : z_iso (F w) x),
             τ w · #G₂ i
             =
             #G₁ i · f).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          repeat (use impred ; intro).
          apply homset_property.
        }
        assert (H := HF₁ x).
        revert H.
        use factor_through_squash.
        {
          apply homset_property.
        }
        intros w.
        induction w as [ w i ].
        use (cancel_z_iso' (functor_on_z_iso G₁ i)).
        exact (!(pr2 φ₁ w i) @ pr2 φ₂ w i).
      Qed.

      Definition enriched_rezk_completion_ump_full_iscontr
        : iscontr
            (∑ (f : G₁ x --> G₂ x),
             ∏ (w : C₁)
               (i : z_iso (F w) x),
             τ w · #G₂ i
             =
             #G₁ i · f).
      Proof.
        assert (H := HF₁ x).
        revert H.
        use factor_through_squash.
        {
          apply isapropiscontr.
        }
        intros w.
        induction w as [ w i ].
        use iscontraprop1.
        - exact enriched_rezk_completion_ump_full_isaprop.
        - simple refine (_ ,, _).
          + exact (#G₁ (inv_from_z_iso i) · τ w · #G₂ i).
          + intros w' i'.
            refine (!(id_right _) @ _).
            rewrite <- (z_iso_after_z_iso_inv (functor_on_z_iso G₂ i)) ; cbn.
            rewrite !assoc.
            apply maponpaths_2.
            rewrite <- functor_comp.
            rewrite !assoc'.
            rewrite <- functor_comp.
            pose (j := invmap
                         (make_weq _ (F_fully_faithful _ _))
                         (i' · inv_from_z_iso i)).
            assert (i' · inv_from_z_iso i = #F j) as p.
            {
              refine (!_).
              apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
            }
            rewrite p.
            exact (!(nat_trans_ax τ _ _ j)).
      Qed.

      Definition enriched_rezk_completion_ump_full_nat_trans_data
        : G₁ x --> G₂ x
        := pr11 enriched_rezk_completion_ump_full_iscontr.

      Definition enriched_rezk_completion_ump_full_nat_trans_eq
                 (w : C₁)
                 (i : z_iso (F w) x)
        : τ w · #G₂ i
          =
          #G₁ i · enriched_rezk_completion_ump_full_nat_trans_data
        := pr21 enriched_rezk_completion_ump_full_iscontr w i.

      Definition enriched_rezk_completion_ump_full_nat_trans_eq_alt
                 (w : C₁)
                 (i : z_iso (F w) x)
        : enriched_rezk_completion_ump_full_nat_trans_data
          =
          #G₁ (inv_from_z_iso i) · τ w · #G₂ i.
      Proof.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (enriched_rezk_completion_ump_full_nat_trans_eq w i).
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        rewrite z_iso_after_z_iso_inv.
        rewrite functor_id.
        apply id_left.
      Qed.

      Proposition eq_to_enriched_rezk_completion_ump_full_nat_trans_data
                  (f : G₁ x --> G₂ x)
                  (p : ∏ (w : C₁)
                         (i : z_iso (F w) x),
                       τ w · #G₂ i
                       =
                       #G₁ i · f)
        : enriched_rezk_completion_ump_full_nat_trans_data = f.
      Proof.
        exact (!(maponpaths
                   pr1
                   (pr2 enriched_rezk_completion_ump_full_iscontr (f ,, p)))).
      Qed.
    End OnOb.

    Proposition enriched_rezk_completion_ump_full_nat_trans_laws
      : is_nat_trans G₁ G₂ enriched_rezk_completion_ump_full_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      assert (H := HF₁ x).
      revert H.
      use factor_through_squash ; [ apply homset_property | ].
      intros wx.
      induction wx as [ wx ix ].
      assert (H := HF₁ y).
      revert H.
      use factor_through_squash ; [ apply homset_property | ].
      intros wy.
      induction wy as [ wy iy ].
      rewrite (enriched_rezk_completion_ump_full_nat_trans_eq_alt x wx ix).
      rewrite (enriched_rezk_completion_ump_full_nat_trans_eq_alt y wy iy).
      rewrite !assoc.
      rewrite <- functor_comp.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply maponpaths.
        refine (!(id_left _) @ _).
        rewrite <- (z_iso_after_z_iso_inv ix).
        apply idpath.
      }
      rewrite !assoc'.
      rewrite functor_comp.
      rewrite !assoc'.
      apply maponpaths.
      pose (j := invmap
                   (make_weq _ (F_fully_faithful _ _))
                   (ix · (f · inv_from_z_iso iy))).
      assert (ix · (f · inv_from_z_iso iy) = #F j) as p.
      {
        refine (!_).
        apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
      }
      rewrite p.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_ax τ _ _ j).
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite <- p.
      rewrite !assoc'.
      apply maponpaths.
      rewrite z_iso_after_z_iso_inv.
      apply id_right.
    Qed.

    Definition enriched_rezk_completion_ump_full_nat_trans
      : G₁ ⟹ G₂.
    Proof.
      use make_nat_trans.
      - exact enriched_rezk_completion_ump_full_nat_trans_data.
      - exact enriched_rezk_completion_ump_full_nat_trans_laws.
    Defined.

    Proposition enriched_rezk_completion_ump_full_nat_trans_enrichment
      : nat_trans_enrichment
          enriched_rezk_completion_ump_full_nat_trans_data
          EG₁ EG₂.
    Proof.
      use nat_trans_enrichment_via_comp.
      intros x y.
      assert (H := HF₁ x).
      revert H.
      use factor_through_squash ; [ apply homset_property | ].
      intros wx.
      induction wx as [ wx ix ].
      assert (H := HF₁ y).
      revert H.
      use factor_through_squash ; [ apply homset_property | ].
      intros wy.
      induction wy as [ wy iy ].
      rewrite (enriched_rezk_completion_ump_full_nat_trans_eq_alt x wx ix).
      rewrite (enriched_rezk_completion_ump_full_nat_trans_eq_alt y wy iy).
      rewrite !precomp_arr_comp, !postcomp_arr_comp.
      rewrite !assoc.
      rewrite (functor_enrichment_precomp_arr EG₂ ix).
      rewrite (functor_enrichment_postcomp_arr EG₁ (inv_from_z_iso iy)).
      use (cancel_z_iso' (_ ,, postcomp_arr_is_z_iso E₂ _ _ (z_iso_is_z_isomorphism iy))).
      cbn.
      rewrite !assoc.
      rewrite <- postcomp_arr_comp.
      rewrite z_iso_inv_after_z_iso.
      rewrite postcomp_arr_id.
      rewrite id_left.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_postcomp_arr.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- precomp_postcomp_arr.
        apply idpath.
      }
      refine (_ @ id_left _).
      rewrite <- precomp_arr_id.
      rewrite <- (z_iso_after_z_iso_inv ix).
      rewrite precomp_arr_comp.
      rewrite !assoc'.
      apply maponpaths.
      use (cancel_z_iso' (_ ,, HF₂ wx wy)) ; cbn.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (nat_trans_enrichment_to_comp Eτ wx wy).
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- functor_enrichment_precomp_arr.
      rewrite !assoc'.
      rewrite <- precomp_postcomp_arr.
      apply idpath.
    Qed.
  End Fullness.

  Proposition enriched_rezk_completion_ump_full
    : full (enriched_precomp E₃ EF).
  Proof.
    intros G₁ G₂ τ.
    simple refine (hinhpr (_ ,, _)).
    - simple refine (_ ,, _).
      + exact (enriched_rezk_completion_ump_full_nat_trans (pr1 τ)).
      + exact (enriched_rezk_completion_ump_full_nat_trans_enrichment (pr1 τ) (pr2 τ)).
    - abstract
        (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         pose (enriched_rezk_completion_ump_full_nat_trans_eq
                 (pr1 τ)
                 (F x) x
                 (identity_z_iso _))
           as p ;
         cbn in p ;
         rewrite !functor_id in p ;
         rewrite id_left, id_right in p ;
         exact (!p)).
  Defined.

  Proposition enriched_rezk_completion_ump_fully_faithful
    : fully_faithful (enriched_precomp E₃ EF).
  Proof.
    use full_and_faithful_implies_fully_faithful.
    split.
    - exact enriched_rezk_completion_ump_full.
    - exact enriched_rezk_completion_ump_faithful.
  Qed.
End PrecompositionFullyFaithful.
