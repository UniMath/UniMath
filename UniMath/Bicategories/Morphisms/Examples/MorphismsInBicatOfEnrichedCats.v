(**
 Morphisms in the bicat of enriched categories

 We characterize several classes of 1-cells in the bicategory of
 enriched categories. One thing to note here, is that the
 'correct' notion of fully faithful enriched functor is stronger
 than the notion of fully faithful 1-cell in the bicategory of
 enriched categories. As such, we don't provide a full
 characterization.

 Contents:
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 3. Conservative 1-cells
 4. Discrete 1-cells
 5. Enriched adjunctions
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentAdjunction.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnitEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(** * 1. Faithful 1-cells *)
Section MorphismsEnrichedCats.
  Context (V : monoidal_cat).

  Definition enriched_cat_faithful_is_faithful_1cell
             {E₁ E₂ : enriched_cat V}
             (F : enriched_functor E₁ E₂)
             (HF : faithful F)
    : faithful_1cell F.
  Proof.
    intros E₃ G₁ G₂ α₁ α₂ p.
    cbn in *.
    use eq_enriched_nat_trans.
    intro x.
    use (invmaponpathsincl _ (HF (pr1 G₁ x) (pr1 G₂ x))).
    exact (maponpaths (λ z, pr11 z x) p).
  Qed.

  Definition enriched_cat_faithful_1cell_is_faithful
             (HV : isTerminal V (I_{V}))
             {E₁ E₂ : enriched_cat V}
             (F : enriched_functor E₁ E₂)
             (HF : faithful_1cell F)
    : faithful F.
  Proof.
    intros x y ; cbn in *.
    use isinclweqonpaths.
    intros f g.
    use isweqimplimpl.
    - intro p.
      refine (from_eq_enriched_nat_trans
                (@faithful_1cell_eq_cell
                    _ _ _ _
                    HF
                    (unit_category ,, unit_enrichment V HV)
                    (constant_functor unit_category (pr1 E₁) x
                     ,,
                     constant_functor_enrichment V HV (pr11 E₁ ,, pr2 E₁) x)
                    (constant_functor unit_category (pr1 E₁) y
                     ,,
                     constant_functor_enrichment V HV (pr11 E₁ ,, pr2 E₁) y)
                    (constant_nat_trans _ f
                     ,,
                     constant_nat_trans_enrichment _ _ _ _)
                    (constant_nat_trans _ g
                     ,,
                     constant_nat_trans_enrichment _ _ _ _)
                    _)
                tt).
      use eq_enriched_nat_trans.
      intro z.
      exact p.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition enriched_cat_faithful_weq_faithful_1cell
             (HV : isTerminal V (I_{V}))
             {E₁ E₂ : enriched_cat V}
             (F : enriched_functor E₁ E₂)
    : faithful F ≃ faithful_1cell F.
  Proof.
    use weqimplimpl.
    - exact (enriched_cat_faithful_is_faithful_1cell F).
    - exact (enriched_cat_faithful_1cell_is_faithful HV F).
    - apply isaprop_faithful.
    - apply isaprop_faithful_1cell.
  Qed.

  (** * 2. Fully faithful 1-cells *)
  Section ToFullyFaithfulCell.
    Context {E₁ E₂ : enriched_cat V}
            {F : enriched_functor E₁ E₂}
            (HF : fully_faithful_enriched_functor
                    (enriched_functor_enrichment F))
            {E₀ : enriched_cat V}
            {G₁ G₂ : enriched_functor E₀ E₁}
            (β : enriched_nat_trans (G₁ · F) (G₂ · F)).

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data
      : nat_trans_data G₁ G₂
      := λ x,
         enriched_to_arr
           E₁
           (enriched_from_arr E₂ (β x)
            · pr1 (HF (G₁ x) (G₂ x))).

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_enrichment
      : nat_trans_enrichment
          enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data
          (enriched_functor_enrichment G₁)
          (enriched_functor_enrichment G₂).
    Proof.
      intros x y.
      cbn.
      unfold enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
      rewrite !enriched_from_to_arr.
      pose (pr2 β x y) as p.
      cbn in p.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply tensor_comp_l_id_r.
      }
      assert (enriched_functor_enrichment F (G₂ x) (G₂ y) #⊗ identity _
              · enriched_comp
                  E₂
                  (F (G₁ x))
                  (F (G₂ x))
                  (F (G₂ y))
              · pr1 (HF _ _)
              =
              id₁ _ #⊗ pr1 (HF (G₁ x) (G₂ x))
              · enriched_comp E₁ (G₁ x) (G₂ x) (G₂ y))
        as X.
      {
        refine (!_).
        use (z_iso_inv_on_left _ _ _ _ (_ ,, _)).
        rewrite !assoc'.
        rewrite (functor_enrichment_comp (pr2 F)).
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite !id_left.
        apply maponpaths.
        refine (!_).
        apply (z_iso_after_z_iso_inv (_ ,, _)).
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (!X).
      }
      clear X.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        apply idpath.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      clear p.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_comp_l_id_r.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_r_id_r.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      use (z_iso_inv_on_left _ _ _ _ (_ ,, _)).
      cbn.
      rewrite !assoc'.
      rewrite (functor_enrichment_comp (enriched_functor_enrichment F)).
      rewrite !assoc.
      apply maponpaths_2.
      refine (_ @ tensor_comp_mor _ _ _ _).
      rewrite id_left.
      apply maponpaths_2.
      refine (!_).
      apply (z_iso_after_z_iso_inv (_ ,, _)).
    Qed.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_laws
      : is_nat_trans
          _ _
          enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
    Proof.
      exact (is_nat_trans_from_enrichment
               enriched_cat_fully_faithful_to_fully_faithful_1cell_enrichment).
    Qed.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans
      : G₁ ⟹ G₂.
    Proof.
      use make_nat_trans.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_laws.
    Defined.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_cell
      : G₁ ==> G₂.
    Proof.
      use make_enriched_nat_trans.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_enrichment.
    Defined.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_eq
      : enriched_cat_fully_faithful_to_fully_faithful_1cell_cell ▹ F = β.
    Proof.
      use eq_enriched_nat_trans.
      intro x.
      cbn.
      unfold enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
      use (invmaponpathsweq (_ ,, isweq_enriched_from_arr E₂ _ _)).
      cbn.
      rewrite (functor_enrichment_from_arr (enriched_functor_enrichment F)).
      rewrite enriched_from_to_arr.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (z_iso_after_z_iso_inv (_ ,, _)).
    Qed.
  End ToFullyFaithfulCell.

  Definition enriched_cat_fully_faithful_to_fully_faithful_1cell
             {E₁ E₂ : enriched_cat V}
             (F : enriched_functor E₁ E₂)
             (HF : fully_faithful_enriched_functor
                     (enriched_functor_enrichment F))
    : fully_faithful_1cell F.
  Proof.
    use make_fully_faithful.
    - apply enriched_cat_faithful_is_faithful_1cell.
      exact (fully_faithful_enriched_functor_to_faithful _ HF).
    - intros E₀ G₁ G₂ β.
      simple refine (_ ,, _).
      + exact (enriched_cat_fully_faithful_to_fully_faithful_1cell_cell HF β).
      + exact (enriched_cat_fully_faithful_to_fully_faithful_1cell_eq HF β).
  Defined.

  (** * 3. Conservative 1-cells *)
  Definition enriched_cat_conservative_to_conservative_1cell
             {E₁ E₂ : enriched_cat V}
             {F : enriched_functor E₁ E₂}
             (HF : conservative F)
     : conservative_1cell F.
   Proof.
     intros E₀ G₁ G₂ τ Hτ.
     use (make_is_invertible_2cell_enriched _).
     intro x.
     apply HF.
     apply (from_is_invertible_2cell_enriched _ (_ ,, Hτ)).
   Defined.

   Definition enriched_cat_conservative_1cell_to_conservative
              (HV : isTerminal V (I_{V}))
              {E₁ E₂ : enriched_cat V}
              {F : enriched_functor E₁ E₂}
              (HF : conservative_1cell F)
     : conservative F.
   Proof.
     intros x y f Hf.
     pose (make_enriched_cat unit_category (unit_enrichment V HV))
       as unit_enriched.
     pose (constant_functor unit_category E₁ x
           ,,
           constant_functor_enrichment V HV (pr11 E₁ ,, pr2 E₁) x
           : unit_enriched --> E₁)
       as G₁.
     pose (constant_functor unit_category (E₁) y
           ,,
           constant_functor_enrichment V HV (pr11 E₁ ,, pr2 E₁) y
           : unit_enriched --> E₁)
       as G₂.
     pose (constant_nat_trans _ f
           ,,
           constant_nat_trans_enrichment _ _ _ _
           : G₁ ==> G₂)
       as τ.
     assert (is_invertible_2cell (τ ▹ F)) as H.
     {
       use (make_is_invertible_2cell_enriched _).
       intro.
       exact Hf.
     }
     pose (nat_z_iso_pointwise_z_iso
             (from_is_invertible_2cell_enriched _ (_ ,, HF _ _ _ _ H))
             tt)
       as p.
     exact (pr2 p).
   Qed.

   Definition enriched_cat_conservative_weq_conservative_1cell
              (HV : isTerminal V (I_{V}))
              {E₁ E₂ : enriched_cat V}
              (F : enriched_functor E₁ E₂)
    : conservative F ≃ conservative_1cell F.
  Proof.
    use weqimplimpl.
    - exact (enriched_cat_conservative_to_conservative_1cell).
    - exact (enriched_cat_conservative_1cell_to_conservative HV).
    - apply isaprop_conservative.
    - apply isaprop_conservative_1cell.
  Qed.

  (** * 4. Discrete 1-cells *)
  Definition enriched_cat_discretee_weq_discrete_1cell
             (HV : isTerminal V (I_{V}))
             {E₁ E₂ : enriched_cat V}
             (F : enriched_functor E₁ E₂)
    : faithful F × conservative F ≃ discrete_1cell F.
  Proof.
    use weqdirprodf.
    - exact (enriched_cat_faithful_weq_faithful_1cell HV F).
    - exact (enriched_cat_conservative_weq_conservative_1cell HV F).
  Qed.
End MorphismsEnrichedCats.

(** * 5. Enriched adjunctions *)
Definition adjunction_enrichment_weq
           {V : monoidal_cat}
           (E₁ E₂ : enriched_cat V)
           (L : adjunction (pr1 E₁) (pr1 E₂))
  : disp_adjunction L (pr2 E₁) (pr2 E₂)
    ≃
    adjunction_enrichment
      (adjunction_weq_adjunction_univ_cats (pr1 E₁) (pr1 E₂) L)
      (pr2 E₁) (pr2 E₂).
Proof.
  use weq_iso.
  - exact (λ LL, pr1 LL ,, pr112 LL ,, pr1 (pr212 LL) ,, pr2 (pr212 LL)).
  - refine (λ LL,
            left_adjoint_enrichment LL
            ,,
            (right_adjoint_enrichment LL
             ,,
             (adjoint_unit_enrichment LL
              ,,
              adjoint_counit_enrichment LL))
            ,,
            _).
    abstract (split ; apply disp_2cell_isapprop_enriched_cats).
  - abstract
      (intro LL ;
       refine (maponpaths (λ z, _ ,, z) _) ;
       use subtypePath ; [ intro ; apply isapropdirprod ; apply disp_cellset_property | ] ;
       apply idpath).
  - abstract
      (intro LL ;
       apply idpath).
Defined.

Definition adjunction_enriched_cats_weq_enriched_adjunction
           {V : monoidal_cat}
           (E₁ E₂ : enriched_cat V)
  : adjunction E₁ E₂ ≃ enriched_adjunction (pr2 E₁) (pr2 E₂)
  := (weqtotal2
        (adjunction_weq_adjunction_univ_cats
           (pr1 E₁) (pr1 E₂))
        (adjunction_enrichment_weq _ _)
      ∘ adjunction_total_disp_weq _ _)%weq.
