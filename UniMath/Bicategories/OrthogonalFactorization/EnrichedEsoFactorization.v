(**********************************************************************************

 The (eso, ff)-factorization system for enriched categories

 In this file, we construct an orthogonal factorization system on the bicategory of
 enriched categories. This classes of maps in this orthogonal factorization system
 are given by the by the essentially surjective enriched functors and by the fully
 faithful enriched functors. The orthogonality says that for every square as follows

<<
         B₁ --------> C₁
         |            |
       F |            | G
         |            |
         V            V
         B₂ --------> C₂
>>

 where `F` is essentially surjective and `G` is fully faithful, there is a unique
 lift up to unique invertible 2-cell.

 In addition, we must give a factorization for every enriched functor as an
 essentially surjective functor followed by a fully faithful functor. For this,
 we use the full image factorization.

 The main challenge of this construction lies in the proof of orthogonality and
 solving the lifting problems. However, the ideas are the same as for categories.
 Let's say that we have the following square that commutes up to natural
 isomorphism:

<<
               Φ₁
         B₁ --------> C₁
         |            |
       F |            | G
         |            |
         V            V
         B₂ --------> C₂
               Φ₂
>>

 Our goal is to construct a lift `B₂ --> C₁`. To do so, we first show that for every
 object `x : B₂` the type of objects `y : C₁` together with an isomorphism
 `G y ≅ Φ₂ x` is contractible ([iscontr_enriched_eso_ff_lift_ob]). The reason why
 we use contractability here, is because it allows us to use the assumption that
 `F` is essentially surjectiev (we can only get a preimage for `x` under `F` if
 we are proving a proposition). For morphisms, we do something similar, but
 expressed using morphisms instead of objects.

 Compared to the case of categories, the additional thing that we must do, is
 constructing an enrichment for our lift. The construction of the enrichment
 follows the proof of functoriality, but expressed in the language of enriched
 categories.

 Finally, as a consequence of this factorization system, we deduce that every
 enriched functor that is essentially surjective and fully faithful, is an adjoint
 equivalence as well. Due to the bicategorical phrasing of our proof, we can only
 use this statement if both the source and target of the functor are univalent
 enriched categories. However, in the proof, we only use that the source of the
 functor is univalent.

 Source: Lemma 4.3.5 in Categorical notions of fibration by Loregian and Riehl.

 Contents
 1, The left and right class of the factorization system
 2. Image factorization
 3. Lifts of 1-cells
 4. Lifts of 2-cells
 5. Uniqueness of lifts of 2-cells
 6. Fully faithful 1-cells are closed under invertible 2-cells
 7. The factorization system
 8. Essentially surjective+fully faithful implies adjoint equivalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.ImageEnriched.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.OrthogonalFactorization.Orthogonality.
Require Import UniMath.Bicategories.OrthogonalFactorization.FactorizationSystem.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedFactorizationSystem.
  Context (V : monoidal_cat).

  (** * 1, The left and right class of the factorization system *)
  Definition enriched_eso_1cell
             (C₁ C₂ : enriched_cat V)
             (F : enriched_functor C₁ C₂)
    : hProp.
  Proof.
    refine (essentially_surjective F ,, _).
    abstract
      (intros ;
       apply isaprop_essentially_surjective).
  Defined.

  Definition enriched_ff_1cell
             (C₁ C₂ : enriched_cat V)
             (F : enriched_functor C₁ C₂)
    : hProp.
  Proof.
    refine (fully_faithful_enriched_functor (enriched_functor_enrichment F) ,, _).
    abstract
      (intros ;
       apply isaprop_fully_faithful_enriched_functor).
  Defined.

  (** * 2. Image factorization *)
  Section Factorization.
    Context {C₁ C₂ : enriched_cat V}
            (F : enriched_functor C₁ C₂).

    Definition enriched_image
      : enriched_cat V.
    Proof.
      use make_enriched_cat.
      - exact (univalent_image F).
      - exact (image_enrichment C₂ F).
    Defined.

    Definition enriched_image_proj
      : enriched_functor C₁ enriched_image.
    Proof.
      use make_enriched_functor.
      - exact (functor_full_img F).
      - exact (image_proj_enrichment (enriched_functor_enrichment F)).
    Defined.

    Definition enriched_image_incl
      : enriched_functor enriched_image C₂.
    Proof.
      use make_enriched_functor.
      - exact (sub_precategory_inclusion _ _).
      - exact (image_incl_enrichment C₂ F).
    Defined.

    Definition enriched_image_comm
      : invertible_2cell (enriched_image_proj · enriched_image_incl) F.
    Proof.
      use make_invertible_2cell.
      - use make_enriched_nat_trans.
        + apply full_image_inclusion_commute_nat_iso.
        + apply image_factorization_enriched_commutes.
      - use make_is_invertible_2cell_enriched.
        intro x.
        apply is_z_isomorphism_identity.
    Defined.

    Definition enriched_eso_ff_factorization
      : factorization_1cell
          enriched_eso_1cell
          enriched_ff_1cell
          F.
    Proof.
      use make_factorization_1cell.
      - exact enriched_image.
      - exact enriched_image_proj.
      - exact enriched_image_incl.
      - apply functor_full_img_essentially_surjective.
      - apply image_incl_enrichment_fully_faithful.
      - exact enriched_image_comm.
    Defined.
  End Factorization.

  Section Lifting.
    Context {B₁ B₂ C₁ C₂ : enriched_cat V}
            (F : enriched_functor B₁ B₂)
            (G : enriched_functor C₁ C₂)
            (HF : enriched_eso_1cell _ _ F)
            (HG : enriched_ff_1cell _ _ G).

    Let G_fully_faithful : fully_faithful G
      := fully_faithful_enriched_functor_to_fully_faithful _ HG.

    (** * 3. Lifts of 1-cells *)
    Section Lift1Cell.
      Context (Φ₁ : enriched_functor B₁ C₁)
              (Φ₂ : enriched_functor B₂ C₂)
              (τ : invertible_2cell (Φ₁ · G) (F · Φ₂)).

      Let τ_iso : nat_z_iso _ _ := from_is_invertible_2cell_enriched _ τ.

      Section OnOb.
        Context (x : B₂).

        Proposition isaprop_enriched_eso_ff_lift_ob
          : isaprop (∑ (y : C₁), z_iso (G y) (Φ₂ x)).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use total2_paths_f.
          - apply (isotoid _).
            + apply univalent_category_is_univalent.
            + exact (make_z_iso'
                       _
                       (fully_faithful_reflects_iso_proof
                          _ _ _
                          G_fully_faithful
                          _ _
                          (z_iso_comp (pr2 φ₁) (z_iso_inv_from_z_iso (pr2 φ₂))))).
          - use subtypePath.
            {
              intro.
              apply isaprop_is_z_isomorphism.
            }
            etrans.
            {
              apply transportf_z_iso_functors.
            }
            rewrite functor_on_inv_from_z_iso.
            use z_iso_inv_on_right.
            refine (!_).
            etrans.
            {
              apply maponpaths_2.
              cbn.
              rewrite idtoiso_isotoid.
              apply (homotweqinvweq (make_weq _ (G_fully_faithful _ _)) _).
            }
            rewrite !assoc'.
            rewrite z_iso_after_z_iso_inv.
            apply id_right.
        Qed.

        Definition iscontr_enriched_eso_ff_lift_ob
          : iscontr (∑ (y : C₁), z_iso (G y) (Φ₂ x)).
        Proof.
          assert (H := HF x).
          revert H.
          use factor_through_squash.
          {
            apply isapropiscontr.
          }
          intros w.
          induction w as [ w f ].
          use iscontraprop1.
          - exact isaprop_enriched_eso_ff_lift_ob.
          - refine (Φ₁ w ,, _).
            exact (z_iso_comp
                     (nat_z_iso_pointwise_z_iso τ_iso w)
                     (functor_on_z_iso Φ₂ f)).
        Qed.

        Definition enriched_eso_ff_lift_ob
          : C₁
          := pr11 iscontr_enriched_eso_ff_lift_ob.

        Definition enriched_eso_ff_lift_z_iso
          : z_iso (G enriched_eso_ff_lift_ob) (Φ₂ x)
          := pr21 iscontr_enriched_eso_ff_lift_ob.
      End OnOb.

      Section OnMor.
        Context {x y : B₂}
                (f : x --> y).

        Definition iscontr_enriched_eso_ff_lift_mor
          : iscontr
              (∑ (g : enriched_eso_ff_lift_ob x --> enriched_eso_ff_lift_ob y),
               #G g
               =
               enriched_eso_ff_lift_z_iso x
               · #Φ₂ f
               · inv_from_z_iso (enriched_eso_ff_lift_z_iso y)).
        Proof.
          use iscontraprop1.
          - use invproofirrelevance.
            intros φ₁ φ₂.
            use subtypePath.
            {
              intro.
              apply homset_property.
            }
            use (invmaponpathsweq (make_weq _ (G_fully_faithful _ _))).
            cbn.
            exact (pr2 φ₁ @ !(pr2 φ₂)).
          - simple refine (_ ,, _).
            + use (invmap (make_weq _ (G_fully_faithful _ _))).
              exact (enriched_eso_ff_lift_z_iso x
                     · # Φ₂ f
                     · inv_from_z_iso (enriched_eso_ff_lift_z_iso y)).
            + apply (homotweqinvweq (make_weq _ (G_fully_faithful _ _))).
        Qed.

        Definition enriched_eso_ff_lift_mor
          : enriched_eso_ff_lift_ob x --> enriched_eso_ff_lift_ob y
          := pr11 iscontr_enriched_eso_ff_lift_mor.

        Definition enriched_eso_ff_lift_mor_eq
          : #G enriched_eso_ff_lift_mor
            =
            enriched_eso_ff_lift_z_iso x
            · #Φ₂ f
            · inv_from_z_iso (enriched_eso_ff_lift_z_iso y)
          := pr21 iscontr_enriched_eso_ff_lift_mor.

        Proposition eq_to_enriched_eso_ff_lift_mor
                    {g : enriched_eso_ff_lift_ob x --> enriched_eso_ff_lift_ob y}
                    (p : #G g
                         =
                         enriched_eso_ff_lift_z_iso x
                         · #Φ₂ f
                         · inv_from_z_iso (enriched_eso_ff_lift_z_iso y))
          : enriched_eso_ff_lift_mor = g.
        Proof.
          exact (!(maponpaths pr1 (pr2 iscontr_enriched_eso_ff_lift_mor (g ,, p)))).
        Qed.
      End OnMor.

      Definition enriched_eso_ff_lift_functor_data
        : functor_data B₂ C₁.
      Proof.
        use make_functor_data.
        - exact (λ x, enriched_eso_ff_lift_ob x).
        - exact (λ x y f, enriched_eso_ff_lift_mor f).
      Defined.

      Proposition enriched_eso_ff_lift_functor_laws
        : is_functor enriched_eso_ff_lift_functor_data.
      Proof.
        split.
        - intro x ; cbn.
          use eq_to_enriched_eso_ff_lift_mor.
          rewrite !functor_id.
          rewrite id_right.
          rewrite z_iso_inv_after_z_iso.
          apply idpath.
        - intros x y z f g ; cbn.
          use eq_to_enriched_eso_ff_lift_mor.
          rewrite !functor_comp.
          rewrite !enriched_eso_ff_lift_mor_eq.
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_left.
          apply idpath.
      Qed.

      Definition enriched_eso_ff_lift_functor
        : B₂ ⟶ C₁.
      Proof.
        use make_functor.
        - exact enriched_eso_ff_lift_functor_data.
        - exact enriched_eso_ff_lift_functor_laws.
      Defined.

      Definition enriched_eso_ff_lift_functor_enrichment_data
        : functor_enrichment_data enriched_eso_ff_lift_functor B₂ C₁
        := λ x y,
           enriched_functor_enrichment Φ₂ x y
           · precomp_arr C₂ _ (enriched_eso_ff_lift_z_iso x)
           · postcomp_arr C₂ _ (inv_from_z_iso (enriched_eso_ff_lift_z_iso y))
           · inv_from_z_iso (fully_faithful_enriched_functor_z_iso HG _ _).

      Arguments enriched_eso_ff_lift_functor_enrichment_data /.

      Proposition enriched_eso_ff_lift_functor_enrichment_laws
        : is_functor_enrichment enriched_eso_ff_lift_functor_enrichment_data.
      Proof.
        repeat split.
        - intros x ; cbn.
          rewrite !assoc.
          rewrite functor_enrichment_id.
          rewrite enriched_id_precomp_arr.
          rewrite enriched_from_arr_postcomp.
          rewrite z_iso_inv_after_z_iso.
          rewrite enriched_from_arr_id.
          refine (_ @ id_right _).
          rewrite <- (z_iso_inv_after_z_iso
                        (fully_faithful_enriched_functor_z_iso
                           HG
                           (enriched_eso_ff_lift_ob x)
                           (enriched_eso_ff_lift_ob x))).
          cbn.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite functor_enrichment_id.
          apply idpath.
        - intros x y z ; cbn.
          rewrite !assoc.
          rewrite functor_enrichment_comp.
          rewrite !assoc'.
          rewrite tensor_comp_mor.
          rewrite !assoc'.
          apply maponpaths.
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
          etrans.
          {
            rewrite !assoc.
            rewrite <- tensor_split.
            rewrite !assoc'.
            apply idpath.
          }
          refine (_ @ id_right _).
          rewrite <- (z_iso_inv_after_z_iso
                        (fully_faithful_enriched_functor_z_iso
                           HG
                           (enriched_eso_ff_lift_ob x)
                           (enriched_eso_ff_lift_ob z))).
          rewrite !assoc ; cbn.
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite functor_enrichment_comp.
          rewrite !assoc.
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            rewrite <- tensor_comp_mor.
            rewrite !assoc'.
            rewrite !z_iso_after_z_iso_inv.
            rewrite !id_right.
            apply maponpaths_2.
            rewrite precomp_postcomp_arr.
            apply idpath.
          }
          rewrite tensor_comp_mor.
          rewrite !assoc'.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite precomp_postcomp_arr_assoc.
          refine (_ @ id_left _).
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- tensor_comp_id_l.
          rewrite <- tensor_id_id.
          apply maponpaths.
          rewrite <- postcomp_arr_comp.
          rewrite <- postcomp_arr_id.
          apply maponpaths.
          apply z_iso_after_z_iso_inv.
        - intros x y f ; cbn.
          rewrite !assoc.
          rewrite <- functor_enrichment_from_arr.
          rewrite enriched_from_arr_precomp.
          rewrite enriched_from_arr_postcomp.
          rewrite <- enriched_eso_ff_lift_mor_eq.
          rewrite (functor_enrichment_from_arr (enriched_functor_enrichment G)).
          rewrite !assoc'.
          refine (!(id_right _) @ !_).
          apply maponpaths.
          exact (z_iso_inv_after_z_iso
                   (fully_faithful_enriched_functor_z_iso HG (enriched_eso_ff_lift_ob x)
                      (enriched_eso_ff_lift_ob y))).
      Qed.

      Definition enriched_eso_ff_lift_functor_enrichment
        : functor_enrichment enriched_eso_ff_lift_functor B₂ C₁.
      Proof.
        simple refine (_ ,, _).
        - exact enriched_eso_ff_lift_functor_enrichment_data.
        - exact enriched_eso_ff_lift_functor_enrichment_laws.
      Defined.

      Definition enriched_eso_ff_lift_enriched_functor
        : enriched_functor B₂ C₁.
      Proof.
        use make_enriched_functor.
        - exact enriched_eso_ff_lift_functor.
        - exact enriched_eso_ff_lift_functor_enrichment.
      Defined.

      Definition enriched_eso_ff_lift_comm1_nat_trans_data
        : nat_trans_data
            (F · enriched_eso_ff_lift_enriched_functor : enriched_functor _ _)
            Φ₁
        := λ x,
           invmap
             (make_weq _ (G_fully_faithful _ _))
             (enriched_eso_ff_lift_z_iso (pr1 (pr1 F) x)
              · inv_from_z_iso (nat_z_iso_pointwise_z_iso τ_iso x)).

      Proposition enriched_eso_ff_lift_comm1_nat_trans_data_eq
                  (x : B₁)
        : #G (enriched_eso_ff_lift_comm1_nat_trans_data x)
          =
          enriched_eso_ff_lift_z_iso (pr1 (pr1 F) x)
          · inv_from_z_iso (nat_z_iso_pointwise_z_iso τ_iso x).
      Proof.
        apply (homotweqinvweq (make_weq _ (G_fully_faithful _ _))).
      Qed.

      Proposition enriched_eso_ff_lift_comm1_nat_trans_laws
        : is_nat_trans _ _ enriched_eso_ff_lift_comm1_nat_trans_data.
      Proof.
        intros x y f.
        use (invmaponpathsweq (make_weq _ (G_fully_faithful _ _))) ; cbn.
        rewrite !functor_comp.
        etrans.
        {
          apply maponpaths.
          apply enriched_eso_ff_lift_comm1_nat_trans_data_eq.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply enriched_eso_ff_lift_comm1_nat_trans_data_eq.
        }
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          exact (!(nat_trans_ax (nat_z_iso_inv τ_iso) _ _ f)).
        }
        refine (!_).
        rewrite !assoc.
        apply maponpaths_2.
        cbn.
        etrans.
        {
          apply maponpaths_2.
          exact (enriched_eso_ff_lift_mor_eq _).
        }
        refine (_ @ id_right _).
        rewrite !assoc'.
        do 2 apply maponpaths.
        apply z_iso_after_z_iso_inv.
      Qed.

      Definition enriched_eso_ff_lift_comm1_nat_trans
        : nat_trans
            (F · enriched_eso_ff_lift_enriched_functor : enriched_functor _ _)
            Φ₁.
      Proof.
        use make_nat_trans.
        - exact enriched_eso_ff_lift_comm1_nat_trans_data.
        - exact enriched_eso_ff_lift_comm1_nat_trans_laws.
      Defined.

      Proposition enriched_eso_ff_lift_comm1_nat_trans_enrichment
        : nat_trans_enrichment
            enriched_eso_ff_lift_comm1_nat_trans
            (enriched_functor_enrichment (F · enriched_eso_ff_lift_enriched_functor))
            (enriched_functor_enrichment Φ₁).
      Proof.
        use nat_trans_enrichment_via_comp.
        intros x y ; cbn.
        rewrite !assoc'.
        refine (!(id_right _) @ _ @ id_right _).
        rewrite <- !(z_iso_inv_after_z_iso (fully_faithful_enriched_functor_z_iso HG _ _)).
        rewrite !assoc.
        apply maponpaths_2 ; cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite <- functor_enrichment_precomp_arr.
          do 2 apply maponpaths.
          exact (enriched_eso_ff_lift_comm1_nat_trans_data_eq x).
        }
        refine (!_).
        etrans.
        {
          do 5 apply maponpaths.
          rewrite <- functor_enrichment_postcomp_arr.
          do 2 apply maponpaths.
          exact (enriched_eso_ff_lift_comm1_nat_trans_data_eq y).
        }
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          apply id_left.
        }
        rewrite <- postcomp_arr_comp.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_left.
          apply idpath.
        }
        rewrite precomp_postcomp_arr.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          exact (!(nat_trans_enrichment_to_comp (τ^-1 : enriched_nat_trans _ _) x y)).
        }
        cbn.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite <- precomp_arr_comp.
        apply idpath.
      Qed.

      Definition enriched_eso_ff_lift_comm1_enriched_nat_trans
        : enriched_nat_trans
            (F · enriched_eso_ff_lift_enriched_functor)
            Φ₁.
      Proof.
        use make_enriched_nat_trans.
        - exact enriched_eso_ff_lift_comm1_nat_trans.
        - exact enriched_eso_ff_lift_comm1_nat_trans_enrichment.
      Defined.

      Definition enriched_eso_ff_lift_comm1_is_nat_z_iso
        : is_nat_z_iso enriched_eso_ff_lift_comm1_nat_trans.
      Proof.
        intros x.
        apply (fully_faithful_reflects_iso_proof
                 _
                 _
                 _
                 _
                 _
                 _
                 (z_iso_comp
                    (enriched_eso_ff_lift_z_iso (F x))
                    (z_iso_inv (nat_z_iso_pointwise_z_iso τ_iso x)))).
      Qed.

      Definition enriched_eso_ff_lift_comm1_nat_z_iso
        : nat_z_iso
            (F · enriched_eso_ff_lift_enriched_functor : enriched_functor _ _)
            Φ₁.
      Proof.
        use make_nat_z_iso.
        - exact enriched_eso_ff_lift_comm1_nat_trans.
        - exact enriched_eso_ff_lift_comm1_is_nat_z_iso.
      Defined.

      Definition enriched_eso_ff_lift_comm1_inv2cell
        : invertible_2cell
            (F · enriched_eso_ff_lift_enriched_functor)
            Φ₁.
      Proof.
        use make_invertible_2cell.
        - exact enriched_eso_ff_lift_comm1_enriched_nat_trans.
        - use make_is_invertible_2cell_enriched.
          apply enriched_eso_ff_lift_comm1_is_nat_z_iso.
      Defined.

      Definition enriched_eso_ff_lift_comm2_nat_trans_data
        : nat_trans_data
            (enriched_eso_ff_lift_enriched_functor · G : enriched_functor _ _)
            Φ₂
        := enriched_eso_ff_lift_z_iso.

      Arguments enriched_eso_ff_lift_comm2_nat_trans_data /.

      Proposition enriched_eso_ff_lift_comm2_is_nat_trans
        : is_nat_trans
            _ _
            enriched_eso_ff_lift_comm2_nat_trans_data.
      Proof.
        intros x y f ; cbn.
        etrans.
        {
          apply maponpaths_2.
          exact (enriched_eso_ff_lift_mor_eq f).
        }
        refine (_ @ id_right _).
        rewrite !assoc'.
        do 2 apply maponpaths.
        apply z_iso_after_z_iso_inv.
      Qed.

      Definition enriched_eso_ff_lift_comm2_nat_trans
        : nat_trans
            (enriched_eso_ff_lift_enriched_functor · G : enriched_functor _ _)
            Φ₂.
      Proof.
        use make_nat_trans.
        - exact enriched_eso_ff_lift_comm2_nat_trans_data.
        - exact enriched_eso_ff_lift_comm2_is_nat_trans.
      Defined.

      Proposition enriched_eso_ff_lift_comm2_nat_trans_enrichment
        : nat_trans_enrichment
            enriched_eso_ff_lift_comm2_nat_trans
            (enriched_functor_enrichment (enriched_eso_ff_lift_enriched_functor · G))
            (enriched_functor_enrichment Φ₂).
      Proof.
        use nat_trans_enrichment_via_comp.
        intros x y ; cbn.
        refine (!(id_right _) @ _).
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          apply id_left.
        }
        rewrite <- postcomp_arr_comp.
        rewrite <- postcomp_arr_id.
        apply maponpaths.
        apply z_iso_after_z_iso_inv.
      Qed.

      Definition enriched_eso_ff_lift_comm2_enriched_nat_trans
        : enriched_nat_trans
            (enriched_eso_ff_lift_enriched_functor · G)
            Φ₂.
      Proof.
        use make_enriched_nat_trans.
        - exact enriched_eso_ff_lift_comm2_nat_trans.
        - exact enriched_eso_ff_lift_comm2_nat_trans_enrichment.
      Defined.

      Definition enriched_eso_ff_lift_comm2_enriched_is_nat_z_iso
        : is_nat_z_iso enriched_eso_ff_lift_comm2_nat_trans.
      Proof.
        intros x.
        apply z_iso_is_z_isomorphism.
      Defined.

      Definition enriched_eso_ff_lift_comm2_inv2cell
        : invertible_2cell (enriched_eso_ff_lift_enriched_functor · G) Φ₂.
      Proof.
        use make_invertible_2cell.
        - exact enriched_eso_ff_lift_comm2_enriched_nat_trans.
        - use make_is_invertible_2cell_enriched.
          apply enriched_eso_ff_lift_comm2_enriched_is_nat_z_iso.
      Defined.

      Proposition enriched_eso_ff_lift_comm_eq
        : (enriched_eso_ff_lift_comm1_inv2cell ▹ G) • τ
          =
          rassociator _ _ _ • (F ◃ enriched_eso_ff_lift_comm2_inv2cell).
      Proof.
        use eq_enriched_nat_trans.
        intros x ; cbn.
        rewrite id_left.
        refine (_ @ id_right _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso τ_iso x))).
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        exact (enriched_eso_ff_lift_comm1_nat_trans_data_eq x).
      Qed.
    End Lift1Cell.

    Definition enriched_eso_ff_lift_1cell
      : orthogonal_essentially_surjective F G.
    Proof.
      intros Φ₁ Φ₂ τ.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact (enriched_eso_ff_lift_enriched_functor Φ₁ Φ₂ τ).
      - exact (enriched_eso_ff_lift_comm1_inv2cell Φ₁ Φ₂ τ).
      - exact (enriched_eso_ff_lift_comm2_inv2cell Φ₁ Φ₂ τ).
      - exact (enriched_eso_ff_lift_comm_eq Φ₁ Φ₂ τ).
    Defined.

    (** * 4. Lifts of 2-cells *)
    Section Lift2Cell.
      Context {L₁ L₂ : enriched_functor B₂ C₁}
              (τ₁ : enriched_nat_trans (F · L₁) (F · L₂))
              (τ₂ : enriched_nat_trans (L₁ · G) (L₂ · G))
              (p : (τ₁ ▹ G) • rassociator F L₂ G
                   =
                   rassociator F L₁ G • (F ◃ τ₂)).

      Section Lift2CellData.
        Context (x : B₂).

        Definition isaprop_enriched_eso_ff_lift_2cell_data
          : isaprop (∑ (f : L₁ x --> L₂ x), #G f = τ₂ x).
        Proof.
          use invproofirrelevance.
          intros f g.
          use subtypePath.
          {
            intro.
            apply homset_property.
          }
          use (invmaponpathsweq (make_weq _ (G_fully_faithful _ _))).
          cbn.
          exact (pr2 f @ !(pr2 g)).
        Qed.

        Definition iscontr_enriched_eso_ff_lift_2cell_data
          : iscontr (∑ (f : L₁ x --> L₂ x), #G f = τ₂ x).
        Proof.
          use iscontraprop1.
          - exact isaprop_enriched_eso_ff_lift_2cell_data.
          - simple refine (_ ,, _).
            + use (invmap (make_weq _ (G_fully_faithful _ _))).
              apply τ₂.
            + cbn.
              exact (homotweqinvweq (make_weq _ (G_fully_faithful _ _)) _).
        Qed.

        Definition iscontr_enriched_eso_ff_lift_2cell_el
          : L₁ x --> L₂ x
          := pr11 iscontr_enriched_eso_ff_lift_2cell_data.

        Proposition iscontr_enriched_eso_ff_lift_2cell_eq
          : #G iscontr_enriched_eso_ff_lift_2cell_el = τ₂ x.
        Proof.
          exact (pr21 iscontr_enriched_eso_ff_lift_2cell_data).
        Qed.

        Proposition eq_to_iscontr_enriched_eso_ff_lift_2cell_el
                    (f : L₁ x --> L₂ x)
                    (q : #G f = τ₂ x)
          : f = iscontr_enriched_eso_ff_lift_2cell_el.
        Proof.
          exact (maponpaths pr1 (pr2 (iscontr_enriched_eso_ff_lift_2cell_data) (f ,, q))).
        Qed.
      End Lift2CellData.

      Proposition is_nat_trans_enriched_eso_ff_lift_2cell_nat_trans
        : is_nat_trans L₁ L₂ iscontr_enriched_eso_ff_lift_2cell_el.
      Proof.
        intros x y f ; cbn.
        use (invmaponpathsweq (make_weq _ (G_fully_faithful _ _))) ; cbn.
        rewrite !functor_comp.
        rewrite !iscontr_enriched_eso_ff_lift_2cell_eq.
        apply (nat_trans_ax τ₂).
      Qed.

      Definition enriched_eso_ff_lift_2cell_nat_trans
        : L₁ ⟹ L₂.
      Proof.
        use make_nat_trans.
        - exact iscontr_enriched_eso_ff_lift_2cell_el.
        - exact is_nat_trans_enriched_eso_ff_lift_2cell_nat_trans.
      Defined.

      Proposition enriched_eso_ff_lift_2cell_enrichment
        : nat_trans_enrichment
            enriched_eso_ff_lift_2cell_nat_trans
            (enriched_functor_enrichment L₁)
            (enriched_functor_enrichment L₂).
      Proof.
        use nat_trans_enrichment_via_comp.
        intros x y.
        refine (!(id_right _) @ _ @ id_right _).
        rewrite <- (z_iso_inv_after_z_iso (_ ,, HG (L₁ x) (L₂ y))) ; cbn.
        rewrite !assoc.
        apply maponpaths_2.
        refine (_ @ nat_trans_enrichment_to_comp τ₂ x y @ _) ; cbn.
        - rewrite !assoc'.
          apply maponpaths.
          rewrite <- functor_enrichment_precomp_arr.
          do 2 apply maponpaths.
          apply iscontr_enriched_eso_ff_lift_2cell_eq.
        - rewrite !assoc'.
          apply maponpaths.
          rewrite <- functor_enrichment_postcomp_arr.
          do 2 apply maponpaths.
          refine (!_).
          apply iscontr_enriched_eso_ff_lift_2cell_eq.
      Qed.

      Definition enriched_eso_ff_lift_2cell_enriched_nat_trans
        : enriched_nat_trans L₁ L₂.
      Proof.
        refine (enriched_eso_ff_lift_2cell_nat_trans ,, enriched_eso_ff_lift_2cell_enrichment).
      Defined.

      Proposition enriched_eso_ff_lift_2cell_enriched_nat_trans_eq_F
        : F ◃ enriched_eso_ff_lift_2cell_enriched_nat_trans = τ₁.
      Proof.
        use eq_enriched_nat_trans.
        intro x ; cbn.
        refine (!_).
        use eq_to_iscontr_enriched_eso_ff_lift_2cell_el.
        pose (from_eq_enriched_nat_trans p x) as q.
        cbn in q.
        rewrite id_right, id_left in q.
        exact q.
      Qed.

      Proposition enriched_eso_ff_lift_2cell_enriched_nat_trans_eq_G
        : enriched_eso_ff_lift_2cell_enriched_nat_trans ▹ G = τ₂.
      Proof.
        use eq_enriched_nat_trans.
        intro x ; cbn.
        apply iscontr_enriched_eso_ff_lift_2cell_eq.
      Qed.
    End Lift2Cell.

    Definition enriched_eso_ff_lift_2cell
      : orthogonal_full F G.
    Proof.
      intros L₁ L₂ τ₁ τ₂ p.
      simple refine (_ ,, _ ,, _).
      - exact (enriched_eso_ff_lift_2cell_enriched_nat_trans τ₂).
      - exact (enriched_eso_ff_lift_2cell_enriched_nat_trans_eq_F _ _ p).
      - exact (enriched_eso_ff_lift_2cell_enriched_nat_trans_eq_G τ₂).
    Defined.

    (** * 5. Uniqueness of lifts of 2-cells *)
    Definition enriched_eso_ff_lift_eq
      : orthogonal_faithful F G.
    Proof.
      intros Φ₁ Φ₂ ζ₁ ζ₂ p q.
      use eq_enriched_nat_trans.
      intro x.
      assert (faithful G) as H.
      {
        exact (fully_faithful_enriched_functor_to_faithful _ HG).
      }
      use (invmaponpathsincl _ (H _ _)).
      exact (from_eq_enriched_nat_trans q x).
    Qed.

    Definition enriched_eso_ff_orthogonal
      : F ⊥ G.
    Proof.
      use make_orthogonal.
      - exact (is_univalent_2_1_bicat_of_enriched_cats V).
      - exact enriched_eso_ff_lift_2cell.
      - exact enriched_eso_ff_lift_eq.
      - exact enriched_eso_ff_lift_1cell.
    Defined.
  End Lifting.

  (** * 6. Fully faithful 1-cells are closed under invertible 2-cells *)
  Section FullyFaithfulInv2cell.
    Context {C₁ C₂ : enriched_cat V}
            {F G : enriched_functor C₁ C₂}
            (τ : invertible_2cell F G)
            (HF : enriched_ff_1cell _ _ F).

    Let τc : enriched_nat_trans _ _ := pr1 τ.
    Let τi : enriched_nat_trans _ _ := τ^-1.

    Local Lemma enriched_fully_faithful_iso_left
                (x : C₁)
      : τi x · τc x = identity _.
    Proof.
      exact (from_eq_enriched_nat_trans (vcomp_linv τ) x).
    Qed.

    Local Lemma enriched_fully_faithful_iso_right
                (x : C₁)
      : τc x · τi x = identity _.
    Proof.
      exact (from_eq_enriched_nat_trans (vcomp_rinv τ) x).
    Qed.

    Definition enriched_fully_faithful_hom_iso
               (x y : C₁)
      : z_iso (C₂ ⦃ F x , F y ⦄) (C₂ ⦃ G x , G y ⦄).
    Proof.
      use make_z_iso.
      - exact (precomp_arr _ _ (τi x) · postcomp_arr _ _ (τc y)).
      - exact (precomp_arr _ _ (τc x) · postcomp_arr _ _ (τi y)).
      - split.
        + abstract
            (rewrite !assoc' ;
             rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
             rewrite <- precomp_postcomp_arr ;
             rewrite !assoc' ;
             rewrite <- postcomp_arr_comp ;
             rewrite !assoc ;
             rewrite <- precomp_arr_comp ;
             rewrite !enriched_fully_faithful_iso_right ;
             rewrite precomp_arr_id ;
             rewrite postcomp_arr_id ;
             apply id_right).
        + abstract
            (rewrite !assoc' ;
             rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
             rewrite <- precomp_postcomp_arr ;
             rewrite !assoc' ;
             rewrite <- postcomp_arr_comp ;
             rewrite !assoc ;
             rewrite <- precomp_arr_comp ;
             rewrite !enriched_fully_faithful_iso_left ;
             rewrite precomp_arr_id ;
             rewrite postcomp_arr_id ;
             apply id_right).
    Defined.

    Definition enriched_fully_faithful_invertible_2cell
      : enriched_ff_1cell _ _ G.
    Proof.
      intros x y.
      assert (enriched_functor_enrichment G x y
              =
              enriched_functor_enrichment F x y · enriched_fully_faithful_hom_iso x y)
        as p.
      {
        cbn.
        rewrite precomp_postcomp_arr.
        rewrite !assoc.
        rewrite <- (nat_trans_enrichment_to_comp τc x y).
        rewrite !assoc'.
        rewrite <- precomp_arr_comp.
        rewrite enriched_fully_faithful_iso_left.
        rewrite precomp_arr_id.
        rewrite id_right.
        apply idpath.
      }
      rewrite p.
      use is_z_isomorphism_comp.
      - apply HF.
      - apply z_iso_is_z_isomorphism.
    Qed.
  End FullyFaithfulInv2cell.

  (** * 7. The factorization system *)
  Definition enriched_eso_ff_orthogonal_factorization_system
    : orthogonal_factorization_system (bicat_of_enriched_cats V).
  Proof.
    use make_orthogonal_factorization_system.
    - exact enriched_eso_1cell.
    - exact enriched_ff_1cell.
    - intros.
      apply propproperty.
    - intros.
      apply propproperty.
    - exact (λ _ _ F, enriched_eso_ff_factorization F).
    - abstract
        (intros C₁ C₂ F G τ HF ; cbn ;
         use (essentially_surjective_nat_z_iso _ HF) ;
         exact (from_is_invertible_2cell_enriched _ τ)).
    - abstract
        (intros C₁ C₂ F G τ HF ; cbn ;
         exact (enriched_fully_faithful_invertible_2cell τ HF)).
    - intros B₁ B₂ C₁ C₂.
      exact enriched_eso_ff_orthogonal.
  Defined.

  (** * 8. Essentially surjective+fully faithful implies adjoint equivalence *)
  Definition enriched_eso_ff_adjoint_equivalence
             {C₁ C₂ : enriched_cat V}
             (F : enriched_functor C₁ C₂)
             (HF₁ : essentially_surjective F)
             (HF₂ : fully_faithful_enriched_functor
                      (enriched_functor_enrichment F))
    : left_adjoint_equivalence F.
  Proof.
    use (orthogonal_left_right_to_adjequiv
           enriched_eso_ff_orthogonal_factorization_system).
    - exact HF₁.
    - exact HF₂.
  Defined.
End EnrichedFactorizationSystem.
