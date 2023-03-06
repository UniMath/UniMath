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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnitEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Faithful 1-cells
 *)
Section MorphismsEnrichedCats.
  Context (V : monoidal_cat).

  Definition enriched_cat_faithful_is_faithful_1cell
             {E₁ E₂ : bicat_of_enriched_cats V}
             (F : E₁ --> E₂)
             (HF : faithful (pr1 F))
    : faithful_1cell F.
  Proof.
    intros E₃ G₁ G₂ α₁ α₂ p.
    cbn in *.
    use subtypePath.
    {
      intro.
      apply isaprop_nat_trans_enrichment.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use (invmaponpathsincl _ (HF (pr1 G₁ x) (pr1 G₂ x))).
    exact (maponpaths (λ z, pr11 z x) p).
  Qed.

  Definition enriched_cat_faithful_1cell_is_faithful
             (HV : isTerminal V (I_{V}))
             {E₁ E₂ : bicat_of_enriched_cats V}
             (F : E₁ --> E₂)
             (HF : faithful_1cell F)
    : faithful (pr1 F).
  Proof.
    intros x y ; cbn in *.
    use isinclweqonpaths.
    intros f g.
    use isweqimplimpl.
    - intro p.
      refine (maponpaths
                (λ z, pr11 z tt)
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
                   _)).
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro z.
      exact p.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition enriched_cat_faithful_weq_faithful_1cell
             (HV : isTerminal V (I_{V}))
             {E₁ E₂ : bicat_of_enriched_cats V}
             (F : E₁ --> E₂)
    : faithful (pr1 F) ≃ faithful_1cell F.
  Proof.
    use weqimplimpl.
    - exact (enriched_cat_faithful_is_faithful_1cell F).
    - exact (enriched_cat_faithful_1cell_is_faithful HV F).
    - apply isaprop_faithful.
    - apply isaprop_faithful_1cell.
  Qed.

  (**
   2. Fully faithful 1-cells
   *)
  Section ToFullyFaithfulCell.
    Context {E₁ E₂ : bicat_of_enriched_cats V}
            {F : E₁ --> E₂}
            (HF : fully_faithful_enriched_functor (pr2 F))
            {E₀ : bicat_of_enriched_cats V}
            {G₁ G₂ : E₀ --> E₁}
            (β : G₁ · F ==> G₂ · F).

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data
      : nat_trans_data
          (pr11 G₁)
          (pr11 G₂)
      := λ x,
         enriched_to_arr
           (pr12 E₁)
           (enriched_from_arr (pr12 E₂) (pr11 β x)
            · pr1 (HF (pr11 G₁ x) (pr11 G₂ x))).

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_enrichment
      : nat_trans_enrichment
          enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data
          (pr2 G₁) (pr2 G₂).
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
      assert (pr12 F (pr11 G₂ x) (pr11 G₂ y) #⊗ identity _
              · enriched_comp
                  (pr12 E₂)
                  (pr11 F (pr11 G₁ x))
                  (pr11 F (pr11 G₂ x))
                  (pr11 F (pr11 G₂ y))
              · pr1 (HF _ _)
              =
              id₁ _ #⊗ pr1 (HF ((pr11 G₁) x) ((pr11 G₂) x))
              · enriched_comp (pr12 E₁) (pr11 G₁ x) (pr11 G₂ x) (pr11 G₂ y))
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
      rewrite (functor_enrichment_comp (pr2 F)).
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
      : pr11 G₁ ⟹ pr11 G₂.
    Proof.
      use make_nat_trans.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_laws.
    Defined.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_cell
      : G₁ ==> G₂.
    Proof.
      simple refine (_ ,, _).
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans.
      - exact enriched_cat_fully_faithful_to_fully_faithful_1cell_enrichment.
    Defined.

    Definition enriched_cat_fully_faithful_to_fully_faithful_1cell_eq
      : enriched_cat_fully_faithful_to_fully_faithful_1cell_cell ▹ F = β.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      cbn.
      unfold enriched_cat_fully_faithful_to_fully_faithful_1cell_nat_trans_data.
      use (invmaponpathsweq (_ ,, isweq_enriched_from_arr (pr2 E₂) _ _)).
      cbn.
      rewrite (functor_enrichment_from_arr (pr2 F)).
      rewrite enriched_from_to_arr.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (z_iso_after_z_iso_inv (_ ,, _)).
    Qed.
  End ToFullyFaithfulCell.

  Definition enriched_cat_fully_faithful_to_fully_faithful_1cell
             {E₁ E₂ : bicat_of_enriched_cats V}
             (F : E₁ --> E₂)
             (HF : fully_faithful_enriched_functor (pr2 F))
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

  (**
   3. Conservative 1-cells
   *)
  Definition enriched_cat_conservative_to_conservative_1cell
             (HV : faithful_moncat V)
             {E₁ E₂ : bicat_of_enriched_cats V}
             {F : E₁ --> E₂}
             (HF : conservative (pr1 F))
     : conservative_1cell F.
   Proof.
     intros E₀ G₁ G₂ τ Hτ.
     use (make_is_invertible_2cell_enriched _ HV).
     intro x.
     apply HF.
     apply (from_is_invertible_2cell_enriched _ (_ ,, Hτ)).
   Defined.

   Definition enriched_cat_conservative_1cell_to_conservative
              (HV : isTerminal V (I_{V}))
              (HV' : faithful_moncat V)
              {E₁ E₂ : bicat_of_enriched_cats V}
              {F : E₁ --> E₂}
              (HF : conservative_1cell F)
     : conservative (pr1 F).
   Proof.
     intros x y f Hf.
     pose (unit_category ,, unit_enrichment V HV : bicat_of_enriched_cats V)
       as unit_enriched.
     pose (constant_functor unit_category (pr11 E₁) x
           ,,
           constant_functor_enrichment V HV (pr11 E₁ ,, pr2 E₁) x
           : unit_enriched --> E₁)
       as G₁.
     pose (constant_functor unit_category (pr11 E₁) y
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
       use (make_is_invertible_2cell_enriched _ HV').
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
              (HV' : faithful_moncat V)
              {E₁ E₂ : bicat_of_enriched_cats V}
              (F : E₁ --> E₂)
    : conservative (pr1 F) ≃ conservative_1cell F.
  Proof.
    use weqimplimpl.
    - exact (enriched_cat_conservative_to_conservative_1cell HV').
    - exact (enriched_cat_conservative_1cell_to_conservative HV HV').
    - apply isaprop_conservative.
    - apply isaprop_conservative_1cell.
  Qed.

  (**
   4. Discrete 1-cells
   *)
  Definition enriched_cat_discretee_weq_discrete_1cell
             (HV : isTerminal V (I_{V}))
             (HV' : faithful_moncat V)
             {E₁ E₂ : bicat_of_enriched_cats V}
             (F : E₁ --> E₂)
    : faithful (pr1 F) × conservative (pr1 F) ≃ discrete_1cell F.
  Proof.
    use weqdirprodf.
    - exact (enriched_cat_faithful_weq_faithful_1cell HV F).
    - exact (enriched_cat_conservative_weq_conservative_1cell HV HV' F).
  Qed.
End MorphismsEnrichedCats.
