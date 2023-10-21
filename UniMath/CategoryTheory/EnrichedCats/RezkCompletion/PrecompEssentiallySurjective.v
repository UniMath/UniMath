(********************************************************************************

 Precomposition is essentially surjective

 To prove the universal property of the Rezk completion of enriched categories,
 we need to prove that precomposition with a weak equivalence gives rise to an
 adjoint equivalence between functor categories to univalent categories. To prove
 this statement, we show that this precomposition functor is both fully faithful
 and essentially surjective. In this file, we prove that it is essentially
 surjective.

 More specifically, we are interested in the following statement:
 Let `F : C₁ ⟶ C₂` be a fully faithful and essentially surjective enriched
 functor. The functor from enriched functor category `C₂ ⟶ C₃` to the enriched
 functor category `C₁ ⟶ C₃` given by precomposition with `F`, is essentially
 surjective.

 The proof of this statement is similar to how the universal property of the Rezk
 completion is proven for ordinary categories. The main idea in this proof is as
 follows. At several points, we need that `F` is essentially surjective. This is
 to find preimages of objects in `C₂` along `F`. However, we can only get such
 preimages if we are proving a proposition, because essential surjective only
 gives the mere existence of preimages. To guarantee that we are proving a
 proposition, we formulate our statements using contractibility. A description of
 how fullness is proven, is given in `PrecompFullyFaithful.v`, and for essential
 surjectivity, the ideas are the same.

 The most interesting part in the proof is constructing the enrichment for the
 functor obtained from the universal property, which is done in
 [enriched_rezk_completion_ump_functor_enrichment]
 Here we again need to make use of contractibility. This is because the enrichment
 of the functor contains an action on the morphisms, but given as a morphism
 between the hom objects. The relevant contractibility statement is given in
 [enriched_rezk_completion_ump_functor_enrichment_iscontr].
 We need to find a morphism in `V`. However, such morphisms aren't unique, so
 we cannot use essential surjectivity. By giving an additional specification for
 the desired morphism, we can guarantee that it is unique, and that allows us to
 use essential surjectivity.

 In essence, the construction is the same as for ordinary categories, except that
 we must use slightly different formulations to take the enrichment into account.

 Contents
 1. Action on objects
 2. Action on morphisms
 3. The enrichment
 4. The commutativity
 5. Essential surjectivity

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.FullyFaithful.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Precomposition.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section PreCompEssentiallySurjective.
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

  Section EssentiallySurjective.
    Context {G : C₁ ⟶ C₃}
            (EG : functor_enrichment G E₁ E₃).

    (** * 1. Action on objects *)
    Section OnOb.
      Context (x : C₂).

      Proposition enriched_rezk_completion_ump_functor_isaprop
                  (w : C₁)
                  (i : z_iso (F w) x)
        : isaprop
            (∑ (y : C₃),
             ∑ (φ : ∏ (w : C₁)
                      (i : z_iso (F w) x),
                   z_iso (G w) y),
             ∏ (w w' : C₁)
               (i : z_iso (F w) x)
               (i' : z_iso (F w') x)
               (k : w --> w')
               (p : #F k · i' = i),
             #G k · φ w' i' = φ w i).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        induction φ₁ as [ y₁ [ φ₁ p₁ ] ].
        induction φ₂ as [ y₂ [ φ₂ p₂ ] ].
        use total2_paths_f ; cbn.
        - exact (isotoid
                   _
                   (univalent_category_is_univalent C₃)
                   (z_iso_comp
                      (z_iso_inv (φ₁ w i))
                      (φ₂ w i))).
        - use subtypePath.
          {
            intro.
            repeat (use impred ; intro).
            apply homset_property.
          }
          rewrite pr1_transportf.
          use funextsec ; intro v.
          rewrite transportf_sec_constant.
          use funextsec ; intro j.
          rewrite transportf_sec_constant.
          rewrite <- idtoiso_postcompose_iso.
          rewrite idtoiso_isotoid.
          use subtypePath.
          {
            intro.
            apply isaprop_is_z_isomorphism.
          }
          cbn.
          pose (k := iso_from_fully_faithful_reflection
                       F_fully_faithful
                       (z_iso_comp j (z_iso_inv i))).
          assert (# F k · i = j) as q.
          {
            etrans.
            {
              apply maponpaths_2.
              apply (homotweqinvweq (weq_from_fully_faithful F_fully_faithful v w)).
            }
            cbn.
            rewrite !assoc'.
            rewrite z_iso_after_z_iso_inv.
            apply id_right.
          }
          refine (_ @ p₂ v w j i k q).
          rewrite !assoc.
          apply maponpaths_2.
          refine (!_).
          use z_iso_inv_on_left.
          refine (!_).
          apply (p₁ v w j i).
          exact q.
      Qed.

      Definition enriched_rezk_completion_ump_functor_iscontr
        : iscontr
            (∑ (y : C₃),
             ∑ (φ : ∏ (w : C₁)
                      (i : z_iso (F w) x),
                   z_iso (G w) y),
             ∏ (w w' : C₁)
               (i : z_iso (F w) x)
               (i' : z_iso (F w') x)
               (k : w --> w')
               (p : #F k · i' = i),
             #G k · φ w' i' = φ w i).
      Proof.
        assert (H := HF₁ x).
        revert H.
        use factor_through_squash ; [ apply isapropiscontr | ].
        intros w.
        induction w as [ w i ].
        use iscontraprop1.
        - exact (enriched_rezk_completion_ump_functor_isaprop w i).
        - simple refine (G w ,, (λ v j, _) ,, _).
          + use (functor_on_z_iso G).
            use (iso_from_fully_faithful_reflection F_fully_faithful).
            exact (z_iso_comp j (z_iso_inv i)).
          + cbn.
            intros v v' j j' l p.
            rewrite <- functor_comp.
            apply maponpaths.
            use (invmaponpathsweq
                   (weq_from_fully_faithful F_fully_faithful _ _)).
            cbn.
            rewrite functor_comp.
            etrans.
            {
              apply maponpaths.
              apply (homotweqinvweq (weq_from_fully_faithful F_fully_faithful _ _)).

            }
            refine (_ @ !(homotweqinvweq (weq_from_fully_faithful F_fully_faithful _ _) _)).
            rewrite !assoc.
            rewrite p.
            apply idpath.
      Qed.

      Definition enriched_rezk_completion_ump_functor_ob
        : C₃
        := pr11 enriched_rezk_completion_ump_functor_iscontr.

      Definition enriched_rezk_completion_ump_functor_iso
                 {w : C₁}
                 (i : z_iso (F w) x)
        : z_iso (G w) enriched_rezk_completion_ump_functor_ob
        := pr121 enriched_rezk_completion_ump_functor_iscontr w i.

      Definition enriched_rezk_completion_ump_functor_eq
                 {w w' : C₁}
                 (i : z_iso (F w) x)
                 (i' : z_iso (F w') x)
                 (k : w --> w')
                 (p : #F k · i' = i)
        : #G k · enriched_rezk_completion_ump_functor_iso i'
          =
          enriched_rezk_completion_ump_functor_iso i
        := pr221 enriched_rezk_completion_ump_functor_iscontr w w' i i' k p.
    End OnOb.

    (** * 2. Action on morphisms *)
    Section OnMor.
      Context {x₁ x₂ : C₂}
              (f : x₁ --> x₂).

      Proposition enriched_rezk_completion_ump_functor_mor_isaprop
                  {v₁ v₂ : C₁}
                  (j₁ : z_iso (F v₁) x₁)
                  (j₂ : z_iso (F v₂) x₂)
        : isaprop
            (∑ (g : enriched_rezk_completion_ump_functor_ob x₁
                    -->
                    enriched_rezk_completion_ump_functor_ob x₂),
             ∏ (w₁ w₂ : C₁)
               (h : w₁ --> w₂)
               (i₁ : z_iso (F w₁) x₁)
               (i₂ : z_iso (F w₂) x₂)
               (p : #F h · i₂ = i₁ · f),
             enriched_rezk_completion_ump_functor_iso x₁ i₁ · g
             =
             #G h · enriched_rezk_completion_ump_functor_iso x₂ i₂).
      Proof.
        pose (k := invmap
                     (make_weq _ (F_fully_faithful _ _))
                     (j₁ · f · inv_from_z_iso j₂)).
        assert (q : # F k · j₂ = j₁ · f).
        {
          unfold k.
          etrans.
          {
            apply maponpaths_2.
            apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
          }
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_right.
          apply idpath.
        }
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          repeat (use impred ; intro).
          apply homset_property.
        }
        use (cancel_z_iso' (enriched_rezk_completion_ump_functor_iso x₁ j₁)).
        exact (pr2 φ₁ v₁ v₂ k j₁ j₂ q @ !(pr2 φ₂ v₁ v₂ k j₁ j₂ q)).
      Qed.

      Definition enriched_rezk_completion_ump_functor_mor_iscontr
        : iscontr
            (∑ (g : enriched_rezk_completion_ump_functor_ob x₁
                    -->
                    enriched_rezk_completion_ump_functor_ob x₂),
             ∏ (w₁ w₂ : C₁)
               (h : w₁ --> w₂)
               (i₁ : z_iso (F w₁) x₁)
               (i₂ : z_iso (F w₂) x₂)
               (p : #F h · i₂ = i₁ · f),
             enriched_rezk_completion_ump_functor_iso x₁ i₁ · g
             =
             #G h · enriched_rezk_completion_ump_functor_iso x₂ i₂).
      Proof.
        assert (H := HF₁ x₁).
        revert H.
        use factor_through_squash ; [ apply isapropiscontr | ].
        intros w₁.
        induction w₁ as [ w₁ i₁ ].
        assert (H := HF₁ x₂).
        revert H.
        use factor_through_squash ; [ apply isapropiscontr | ].
        intros w₂.
        induction w₂ as [ w₂ i₂ ].
        pose (j := invmap
                     (make_weq _ (F_fully_faithful _ _))
                     (i₁ · f · inv_from_z_iso i₂)).
        use iscontraprop1.
        - exact (enriched_rezk_completion_ump_functor_mor_isaprop i₁ i₂).
        - simple refine (_ ,, _).
          + exact (inv_from_z_iso (enriched_rezk_completion_ump_functor_iso x₁ i₁)
                   · #G j
                   · enriched_rezk_completion_ump_functor_iso x₂ i₂).
          + intros w₁' w₂' h i₁' i₂' p.
            pose (k₁ := invmap
                          (make_weq _ (F_fully_faithful _ _))
                          (i₁' · inv_from_z_iso i₁)).
            assert (# F k₁ · i₁ = i₁') as q₁.
            {
              etrans.
              {
                apply maponpaths_2.
                apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
              }
              rewrite !assoc'.
              rewrite z_iso_after_z_iso_inv.
              apply id_right.
            }
            pose (k₂ := invmap
                          (make_weq _ (F_fully_faithful _ _))
                          (i₂' · inv_from_z_iso i₂)).
            assert (# F k₂ · i₂ = i₂') as q₂.
            {
              etrans.
              {
                apply maponpaths_2.
                apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
              }
              rewrite !assoc'.
              rewrite z_iso_after_z_iso_inv.
              apply id_right.
            }
            rewrite <- (enriched_rezk_completion_ump_functor_eq x₁ i₁' i₁ k₁ q₁).
            rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              rewrite !assoc.
              rewrite z_iso_inv_after_z_iso.
              rewrite id_left.
              apply idpath.
            }
            rewrite <- (enriched_rezk_completion_ump_functor_eq x₂ i₂' i₂ k₂ q₂).
            rewrite !assoc.
            apply maponpaths_2.
            rewrite <- !functor_comp.
            apply maponpaths.
            use (invmaponpathsweq
                   (weq_from_fully_faithful F_fully_faithful _ _)).
            cbn.
            rewrite !functor_comp.
            etrans.
            {
              apply maponpaths_2.
              apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
            }
            etrans.
            {
              apply maponpaths.
              apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
            }
            refine (!_).
            etrans.
            {
              apply maponpaths.
              apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
            }
            rewrite !assoc.
            rewrite p.
            rewrite !assoc'.
            apply maponpaths.
            rewrite !assoc.
            rewrite z_iso_after_z_iso_inv.
            rewrite id_left.
            apply idpath.
      Qed.

      Definition enriched_rezk_completion_ump_functor_mor
        : enriched_rezk_completion_ump_functor_ob x₁
          -->
          enriched_rezk_completion_ump_functor_ob x₂
        := pr11 enriched_rezk_completion_ump_functor_mor_iscontr.

      Proposition enriched_rezk_completion_ump_functor_mor_eq
                  {w₁ w₂ : C₁}
                  (h : w₁ --> w₂)
                  (i₁ : z_iso (F w₁) x₁)
                  (i₂ : z_iso (F w₂) x₂)
                  (p : #F h · i₂ = i₁ · f)
        : enriched_rezk_completion_ump_functor_iso x₁ i₁
          · enriched_rezk_completion_ump_functor_mor
          =
          #G h · enriched_rezk_completion_ump_functor_iso x₂ i₂.
      Proof.
        exact (pr21 enriched_rezk_completion_ump_functor_mor_iscontr w₁ w₂ h i₁ i₂ p).
      Qed.

      Proposition eq_to_enriched_rezk_completion_ump_functor_mor
                  (g : enriched_rezk_completion_ump_functor_ob x₁
                       -->
                       enriched_rezk_completion_ump_functor_ob x₂)
                  (p : ∏ (w₁ w₂ : C₁)
                         (h : w₁ --> w₂)
                         (i₁ : z_iso (F w₁) x₁)
                         (i₂ : z_iso (F w₂) x₂)
                         (p : #F h · i₂ = i₁ · f),
                       enriched_rezk_completion_ump_functor_iso x₁ i₁ · g
                       =
                       #G h · enriched_rezk_completion_ump_functor_iso x₂ i₂)
        : enriched_rezk_completion_ump_functor_mor
          =
          g.
      Proof.
        exact (!(maponpaths
                   pr1
                   (pr2 enriched_rezk_completion_ump_functor_mor_iscontr (g ,, p)))).
      Qed.
    End OnMor.

    Definition enriched_rezk_completion_ump_functor_data
      : functor_data C₂ C₃.
    Proof.
      use make_functor_data.
      - exact enriched_rezk_completion_ump_functor_ob.
      - exact (λ _ _ f, enriched_rezk_completion_ump_functor_mor f).
    Defined.

    Proposition enriched_rezk_completion_ump_functor_laws
      : is_functor enriched_rezk_completion_ump_functor_data.
    Proof.
      split.
      - intro x ; cbn.
        use eq_to_enriched_rezk_completion_ump_functor_mor.
        intros w₁ w₂ h i₁ i₂ p.
        rewrite id_right in p.
        rewrite id_right.
        rewrite (enriched_rezk_completion_ump_functor_eq x i₁ i₂ _ p).
        apply idpath.
      - intros x y z f g ; cbn.
        use eq_to_enriched_rezk_completion_ump_functor_mor.
        intros wx wz h ix iz p.
        assert (H := HF₁ y).
        revert H.
        use factor_through_squash ; [ apply homset_property | ].
        intros wy.
        induction wy as [ wy iy ].
        pose (j := invmap
                     (make_weq _ (F_fully_faithful _ _))
                     (ix · f · inv_from_z_iso iy)).
        assert (# F j · iy = ix · f) as q.
        {
          etrans.
          {
            apply maponpaths_2.
            apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
          }
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_right.
          apply idpath.
        }
        pose (k := invmap
                     (make_weq _ (F_fully_faithful _ _))
                     (iy · g · inv_from_z_iso iz)).
        assert (# F k · iz = iy · g) as r.
        {
          etrans.
          {
            apply maponpaths_2.
            apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
          }
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_right.
          apply idpath.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (enriched_rezk_completion_ump_functor_mor_eq f j ix iy q).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact (enriched_rezk_completion_ump_functor_mor_eq g k iy iz r).
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- functor_comp.
        apply maponpaths.
        use (invmaponpathsweq
               (weq_from_fully_faithful F_fully_faithful _ _)).
        cbn.
        rewrite functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
        }
        etrans.
        {
          apply maponpaths.
          apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
        }
        refine (_ @ id_right _).
        rewrite <- (z_iso_inv_after_z_iso iz).
        rewrite !assoc.
        apply maponpaths_2.
        rewrite p.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
    Qed.

    Definition enriched_rezk_completion_ump_functor
      : C₂ ⟶ C₃.
    Proof.
      use make_functor.
      - exact enriched_rezk_completion_ump_functor_data.
      - exact enriched_rezk_completion_ump_functor_laws.
    Defined.

    (** * 3. The enrichment *)
    Definition enriched_rezk_completion_ump_functor_enrichment_iscontr
               (x y : C₂)
      : iscontr
          (∑ (f : E₂ ⦃ x , y ⦄
                  -->
                  E₃ ⦃ enriched_rezk_completion_ump_functor x
                     , enriched_rezk_completion_ump_functor y ⦄),
           ∏ (wx wy : C₁)
             (ix : z_iso (F wx) x)
             (iy : z_iso (F wy) y),
           f
           =
           precomp_arr E₂ _ ix
           · postcomp_arr E₂ _ (inv_from_z_iso iy)
           · inv_from_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)
           · EG wx wy
           · precomp_arr E₃ _ (inv_from_z_iso (enriched_rezk_completion_ump_functor_iso x ix))
           · postcomp_arr E₃ _ (enriched_rezk_completion_ump_functor_iso y iy)).
    Proof.
      assert (H := HF₁ x).
      revert H.
      use factor_through_squash ; [ apply isapropiscontr | ].
      intros wx.
      induction wx as [ wx ix ].
      assert (H := HF₁ y).
      revert H.
      use factor_through_squash ; [ apply isapropiscontr | ].
      intros wy.
      induction wy as [ wy iy ].
      use iscontraprop1.
      - use invproofirrelevance.
        intros φ₁ φ₂.
        induction φ₁ as [ φ₁ p₁ ].
        induction φ₂ as [ φ₂ p₂ ].
        use subtypePath.
        {
          intro.
          repeat (use impred ; intro).
          apply homset_property.
        }
        exact (p₁ wx wy ix iy @ !(p₂ wx wy ix iy)).
      - simple refine (_ ,, _).
        + exact (postcomp_arr E₂ _ (inv_from_z_iso iy)
                 · precomp_arr E₂ _ ix
                 · inv_from_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)
                 · EG wx wy
                 · postcomp_arr E₃ _ (enriched_rezk_completion_ump_functor_iso y iy)
                 · precomp_arr E₃ _ (inv_from_z_iso
                                       (enriched_rezk_completion_ump_functor_iso x ix))).
        + intros wx' wy' ix' iy'.
          rewrite <- precomp_postcomp_arr.
          refine (!(id_left _) @ _).
          rewrite <- precomp_arr_id.
          rewrite <- (z_iso_after_z_iso_inv ix').
          rewrite precomp_arr_comp.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- precomp_arr_comp.
          refine (!(id_left _) @ _).
          rewrite <- postcomp_arr_id.
          rewrite <- (z_iso_after_z_iso_inv iy').
          rewrite postcomp_arr_comp.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- precomp_postcomp_arr.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- postcomp_arr_comp.
            apply idpath.
          }
          refine (!(id_left _) @ _).
          rewrite <- (z_iso_after_z_iso_inv
                        (fully_faithful_enriched_functor_z_iso HF₂ wx' wy')) ; cbn.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          pose (jx := invmap
                         (make_weq _ (F_fully_faithful _ _))
                         (ix · inv_from_z_iso ix')).
          assert (ix · inv_from_z_iso ix' = #F jx) as px.
          {
            refine (!_).
            apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
          }
          rewrite px.
          rewrite functor_enrichment_precomp_arr.
          pose (jy := invmap
                        (make_weq _ (F_fully_faithful _ _))
                        (iy' · inv_from_z_iso iy)).
          assert (iy' · inv_from_z_iso iy = #F jy) as py.
          {
            refine (!_).
            apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
          }
          rewrite py.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite functor_enrichment_postcomp_arr.
            rewrite !assoc'.
            apply maponpaths.
            rewrite !assoc.
            do 3 apply maponpaths_2.
            apply (z_iso_inv_after_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)).
          }
          rewrite id_left.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- functor_enrichment_postcomp_arr.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- functor_enrichment_precomp_arr.
          rewrite !assoc'.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- postcomp_arr_comp.
            rewrite <- precomp_postcomp_arr.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- precomp_arr_comp.
          etrans.
          {
            do 2 apply maponpaths.
            refine (enriched_rezk_completion_ump_functor_eq _ iy' _ _ _).
            rewrite <- py.
            rewrite !assoc'.
            rewrite z_iso_after_z_iso_inv.
            apply id_right.
          }
          apply maponpaths_2.
          apply maponpaths.
          use z_iso_inv_on_right.
          use z_iso_inv_on_left.
          refine (!_).
          use enriched_rezk_completion_ump_functor_eq.
          rewrite <- px.
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          apply id_right.
    Qed.

    Definition enriched_rezk_completion_ump_functor_enrichment_data
      : functor_enrichment_data
          enriched_rezk_completion_ump_functor
          E₂
          E₃
      := λ x y,
         pr11 (enriched_rezk_completion_ump_functor_enrichment_iscontr x y).

    Proposition enriched_rezk_completion_ump_functor_enrichment_eq
                {x y : C₂}
                {wx wy : C₁}
                (ix : z_iso (F wx) x)
                (iy : z_iso (F wy) y)
      : enriched_rezk_completion_ump_functor_enrichment_data x y
        =
        precomp_arr E₂ _ ix
        · postcomp_arr E₂ _ (inv_from_z_iso iy)
        · inv_from_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)
        · EG wx wy
        · precomp_arr E₃ _ (inv_from_z_iso (enriched_rezk_completion_ump_functor_iso x ix))
        · postcomp_arr E₃ _ (enriched_rezk_completion_ump_functor_iso y iy).
    Proof.
      exact (pr21 (enriched_rezk_completion_ump_functor_enrichment_iscontr x y) wx wy ix iy).
    Qed.

    Proposition eq_to_enriched_rezk_completion_ump_functor_enrichment_data
                {x y : C₂}
                (f : E₂ ⦃ x , y ⦄
                     -->
                     E₃ ⦃ enriched_rezk_completion_ump_functor x
                        , enriched_rezk_completion_ump_functor y ⦄)
                (p : ∏ (wx wy : C₁)
                       (ix : z_iso (F wx) x)
                       (iy : z_iso (F wy) y),
                     f
                     =
                     precomp_arr E₂ _ ix
                     · postcomp_arr E₂ _ (inv_from_z_iso iy)
                     · inv_from_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)
                     · EG wx wy
                     · precomp_arr
                         E₃
                         _
                         (inv_from_z_iso (enriched_rezk_completion_ump_functor_iso x ix))
                     · postcomp_arr E₃ _ (enriched_rezk_completion_ump_functor_iso y iy))
      : enriched_rezk_completion_ump_functor_enrichment_data x y = f.
    Proof.
      exact (!(maponpaths
                 pr1
                 (pr2 (enriched_rezk_completion_ump_functor_enrichment_iscontr x y) (f ,, p)))).
    Qed.

    Proposition enriched_rezk_completion_ump_functor_enrichment_laws
      : is_functor_enrichment enriched_rezk_completion_ump_functor_enrichment_data.
    Proof.
      repeat split.
      - intro x.
        assert (H := HF₁ x).
        revert H.
        use factor_through_squash ; [ apply homset_property | ].
        intros w.
        induction w as [ w i ].
        rewrite (enriched_rezk_completion_ump_functor_enrichment_eq i i).
        rewrite !assoc.
        rewrite enriched_id_precomp_arr.
        rewrite enriched_from_arr_postcomp.
        rewrite z_iso_inv_after_z_iso.
        rewrite enriched_from_arr_id.
        rewrite <- (functor_enrichment_id EF).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 3 apply maponpaths_2.
          exact (z_iso_inv_after_z_iso (fully_faithful_enriched_functor_z_iso HF₂ w w)).
        }
        rewrite id_left.
        rewrite !assoc.
        rewrite functor_enrichment_id.
        rewrite enriched_id_precomp_arr.
        rewrite enriched_from_arr_postcomp.
        rewrite z_iso_after_z_iso_inv.
        rewrite enriched_from_arr_id.
        apply idpath.
      - intros x y z ; cbn.
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
        assert (H := HF₁ z).
        revert H.
        use factor_through_squash ; [ apply homset_property | ].
        intros wz.
        induction wz as [ wz iz ].
        rewrite (enriched_rezk_completion_ump_functor_enrichment_eq ix iz).
        rewrite (enriched_rezk_completion_ump_functor_enrichment_eq ix iy).
        rewrite (enriched_rezk_completion_ump_functor_enrichment_eq iy iz).
        etrans.
        {
          rewrite !assoc.
          rewrite enriched_comp_precomp_arr.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite enriched_comp_postcomp_arr.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- tensor_split.
          apply idpath.
        }
        refine (_ @ id_left _).
        rewrite <- tensor_id_id.
        rewrite <- postcomp_arr_id.
        rewrite <- precomp_arr_id.
        rewrite <- (z_iso_after_z_iso_inv iz).
        rewrite <- (z_iso_after_z_iso_inv ix).
        rewrite postcomp_arr_comp.
        rewrite precomp_arr_comp.
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite !assoc.
            rewrite <- precomp_postcomp_arr.
            rewrite !assoc'.
            apply maponpaths.
            rewrite !assoc.
            rewrite <- postcomp_arr_comp.
            rewrite z_iso_inv_after_z_iso.
            rewrite postcomp_arr_id.
            rewrite id_left.
            apply idpath.
          }
          apply maponpaths.
          rewrite !assoc.
          rewrite <- precomp_arr_comp.
          rewrite z_iso_inv_after_z_iso.
          rewrite precomp_arr_id.
          rewrite id_left.
          apply idpath.
        }
        etrans.
        {
          rewrite !assoc'.
          rewrite tensor_comp_mor.
          apply idpath.
        }
        refine (_ @ id_left _).
        rewrite <- tensor_id_id.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite <- precomp_arr_id.
            rewrite <- (z_iso_after_z_iso_inv iy).
            rewrite precomp_arr_comp.
            apply idpath.
          }
          rewrite <- postcomp_arr_id.
          rewrite <- (z_iso_after_z_iso_inv iy).
          rewrite postcomp_arr_comp.
          rewrite tensor_comp_mor.
          apply idpath.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          do 4 apply maponpaths_2.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite precomp_postcomp_arr_assoc.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite <- postcomp_arr_comp.
          rewrite z_iso_inv_after_z_iso.
          rewrite postcomp_arr_id.
          rewrite tensor_id_id.
          apply id_left.
        }
        rewrite tensor_comp_mor.
        refine (!(id_left _) @ _).
        rewrite !assoc'.
        rewrite <- tensor_id_id.
        rewrite <- (z_iso_after_z_iso_inv (fully_faithful_enriched_functor_z_iso HF₂ wy wz)).
        rewrite <- (z_iso_after_z_iso_inv (fully_faithful_enriched_functor_z_iso HF₂ wx wy)).
        cbn.
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_comp.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          do 3 apply maponpaths_2.
          apply (z_iso_inv_after_z_iso
                   (fully_faithful_enriched_functor_z_iso HF₂ wx wz)).
        }
        rewrite id_left.
        rewrite !assoc.
        rewrite functor_enrichment_comp.
        rewrite !assoc'.
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite enriched_comp_precomp_arr.
        rewrite !assoc'.
        rewrite enriched_comp_postcomp_arr.
        rewrite !assoc.
        rewrite <- tensor_split.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply precomp_postcomp_arr.
        }
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite precomp_postcomp_arr_assoc.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite <- postcomp_arr_comp.
        rewrite z_iso_inv_after_z_iso.
        rewrite postcomp_arr_id.
        rewrite tensor_id_id.
        apply id_left.
      - intros x y f ; cbn.
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
        rewrite (enriched_rezk_completion_ump_functor_enrichment_eq ix iy).
        rewrite !assoc.
        rewrite enriched_from_arr_precomp.
        rewrite enriched_from_arr_postcomp.
        pose (j := invmap
                     (make_weq _ (F_fully_faithful _ _))
                     (ix · f · inv_from_z_iso iy)).
        assert (ix · f · inv_from_z_iso iy = #F j) as q.
        {
          refine (!_).
          apply (homotweqinvweq (make_weq _ (F_fully_faithful _ _))).
        }
        rewrite q.
        rewrite (functor_enrichment_from_arr EF).
        refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          do 3 apply maponpaths_2.
          apply (z_iso_inv_after_z_iso (fully_faithful_enriched_functor_z_iso HF₂ _ _)).
        }
        rewrite id_left.
        rewrite !assoc.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_precomp.
        rewrite enriched_from_arr_postcomp.
        apply maponpaths.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(enriched_rezk_completion_ump_functor_mor_eq f j ix iy _)).
          rewrite <- q.
          rewrite !assoc'.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_right.
          apply idpath.
        }
        rewrite !assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
    Qed.

    Definition enriched_rezk_completion_ump_functor_enrichment
      : functor_enrichment enriched_rezk_completion_ump_functor E₂ E₃.
    Proof.
      simple refine (_ ,, _).
      - exact enriched_rezk_completion_ump_functor_enrichment_data.
      - exact enriched_rezk_completion_ump_functor_enrichment_laws.
    Defined.

    Definition enriched_rezk_completion_ump_enriched_functor
      : enriched_functor_category E₂ E₃
      := enriched_rezk_completion_ump_functor
         ,,
         enriched_rezk_completion_ump_functor_enrichment.

    (** * 4. The commutativity *)
    Proposition enriched_rezk_completion_ump_comm_laws
      : is_nat_trans
          G
          (F ∙ enriched_rezk_completion_ump_functor)
          (λ x, enriched_rezk_completion_ump_functor_iso (F x) (identity_z_iso (F x))).
    Proof.
      intros x y f ; cbn.
      refine (!_).
      refine (enriched_rezk_completion_ump_functor_mor_eq _ f _ (identity_z_iso _) _).
      cbn.
      rewrite id_right, id_left.
      apply idpath.
    Qed.

    Definition enriched_rezk_completion_ump_comm
      : G ⟹ F ∙ enriched_rezk_completion_ump_functor.
    Proof.
      use make_nat_trans.
      - exact (λ x, enriched_rezk_completion_ump_functor_iso (F x) (identity_z_iso _)).
      - exact enriched_rezk_completion_ump_comm_laws.
    Defined.

    Definition enriched_rezk_completion_ump_nat_z_iso
      : nat_z_iso G (F ∙ enriched_rezk_completion_ump_functor).
    Proof.
      use make_nat_z_iso.
      - exact enriched_rezk_completion_ump_comm.
      - intro.
        apply z_iso_is_z_isomorphism.
    Defined.

    Proposition enriched_rezk_completion_ump_comm_enrichment
      : nat_trans_enrichment
          enriched_rezk_completion_ump_nat_z_iso
          EG
          (functor_comp_enrichment
             EF
             enriched_rezk_completion_ump_functor_enrichment).
    Proof.
      use nat_trans_enrichment_via_comp.
      intros x y ; cbn.
      rewrite (enriched_rezk_completion_ump_functor_enrichment_eq
                 (identity_z_iso (F x))
                 (identity_z_iso (F y))) ; cbn.
      rewrite precomp_arr_id, postcomp_arr_id.
      rewrite !id_left.
      rewrite !assoc.
      etrans.
      {
        do 4 apply maponpaths_2.
        exact (z_iso_inv_after_z_iso
                 (fully_faithful_enriched_functor_z_iso HF₂ x y)).
      }
      rewrite id_left.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      rewrite <- precomp_arr_comp.
      rewrite z_iso_inv_after_z_iso.
      rewrite precomp_arr_id.
      apply id_left.
    Qed.

    Proposition enriched_rezk_completion_ump_comm_inv_enrichment
      : nat_trans_enrichment
          (nat_z_iso_inv enriched_rezk_completion_ump_nat_z_iso)
          (functor_comp_enrichment
             EF
             enriched_rezk_completion_ump_functor_enrichment)
          EG.
    Proof.
      apply nat_z_iso_inv_enrichment.
      apply enriched_rezk_completion_ump_comm_enrichment.
    Qed.
  End EssentiallySurjective.

  (** * 5. Essential surjectivity *)
  Proposition enriched_rezk_completion_ump_essentially_surjective
    : essentially_surjective (enriched_precomp E₃ EF).
  Proof.
    intros G.
    refine (hinhpr (enriched_rezk_completion_ump_enriched_functor (pr2 G) ,, _)).
    use make_z_iso.
    - simple refine (_ ,, _) ; cbn.
      + exact (nat_z_iso_inv enriched_rezk_completion_ump_nat_z_iso).
      + exact (enriched_rezk_completion_ump_comm_inv_enrichment _).
    - refine (enriched_rezk_completion_ump_comm ,, _).
      exact (enriched_rezk_completion_ump_comm_enrichment _).
    - split.
      + abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           apply z_iso_after_z_iso_inv).
      + abstract
          (use subtypePath ; [ intro ; apply isaprop_nat_trans_enrichment | ] ;
           use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           apply z_iso_inv_after_z_iso).
  Defined.
End PreCompEssentiallySurjective.
