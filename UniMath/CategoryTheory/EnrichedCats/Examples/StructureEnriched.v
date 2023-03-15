(*****************************************************************

 Enrichment over structured sets

 In this file, we look at categories enriched over a notion of
 structured sets. The notion of structured sets in consideration
 here, is designed so that structures are preserved under product
 and the unit set has a structure. As such, we have a cartesian
 monoidal category of structured sets (`StructuresMonoidal.v`).

 We first show that this monoidal category is faithful. From this,
 it follows that all natural transformations are enriched, so
 afterwards we don't consider enriched transformations.

 Afterwards, we give an elementary definition of enrichment over
 structures. This elementary notion says that for every homset,
 we have a structure and that composition preserves the structure.
 This notion of enrichment is equivalent to the usual one.

 Lastly, we do the same for enriched functors, and for those,
 enrichment is the same as the action on morphisms being a
 structure-preserving map. Again this is equivalent to the
 general definition of enrichment.

 We can apply the content of this file to various notions of
 structured sets, such as posets and domains. However, note that
 not for every notion of structured set this gives the 'right'
 notion of enriched category. For example, for abelian groups
 (or modules), the corresponding notion of enriched category
 should be over a different monoidal category than the one
 induced by the cartesian structure of these categories. For these
 notions of structure, one should construct the tensor product
 instead and show that this gives rise to a monoidal category.

 Contents
 1. The monoidal category is faithful
 2. Elementary definition of enrichment over structures
 3. Equivalence of enrichments with the elementary definition
 4. Elementary definition of functor enrichments over structures
 5. Equivalence of functor enrichments with elementary definition

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.StructureWithProd.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.StructuresMonoidal.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.

Local Open Scope cat.

Definition homset
           {C : category}
           (x y : C)
  : hSet
  := x --> y ,, homset_property C x y.

Section FixAStructure.
  Context (P : hset_struct).

  (**
   1. The monoidal category is faithful
   *)
  Definition category_of_hset_struct_faithful_moncat
    : faithful_moncat (monoidal_cat_of_hset_struct P).
  Proof.
    intros R₁ R₂ f g p.
    use subtypePath.
    {
      intro ; cbn -[isaprop].
      apply isaprop_hset_struct_on_mor.
    }
    use funextsec ; intro x.
    assert (mor_hset_struct P (hset_struct_unit P) (pr2 R₁) (λ _, x)) as H.
    {
      apply hset_struct_const.
    }
    exact (eqtohomot (maponpaths pr1 (p ((λ _, x) ,, H))) tt).
  Qed.

  (**
   2. Elementary definition of enrichment over structures
   *)
  Definition struct_enrichment_data
             (C : category)
    : UU
    := ∏ (x y : C), P (homset x y).

  Definition struct_enrichment_laws
             {C : category}
             (SC : struct_enrichment_data C)
    : UU
    := ∏ (x y z : C),
       mor_hset_struct
         P
         (hset_struct_prod P (SC y z) (SC x y))
         (SC x z)
         (λ (fg : C ⟦ y, z ⟧ × C ⟦ x, y ⟧), pr2 fg · pr1 fg).

  Proposition isaprop_struct_enrichment_laws
              {C : category}
              (SC : struct_enrichment_data C)
    : isaprop (struct_enrichment_laws SC).
  Proof.
    repeat (use impred ; intro).
    apply isaprop_hset_struct_on_mor.
  Qed.

  Definition struct_enrichment
             (C : category)
    : UU
    := ∑ (SC : struct_enrichment_data C),
       struct_enrichment_laws SC.

  Definition struct_enrichment_to_data
             {C : category}
             (SC : struct_enrichment C)
             (x y : C)
    : P (homset x y)
    := pr1 SC x y.

  Coercion struct_enrichment_to_data : struct_enrichment >-> Funclass.

  Proposition struct_enrichment_comp
              {C : category}
              (SC : struct_enrichment C)
              (x y z : C)
    : mor_hset_struct
        P
        (hset_struct_prod P (SC y z) (SC x y))
        (SC x z)
        (λ (fg : C ⟦ y, z ⟧ × C ⟦ x, y ⟧), pr2 fg · pr1 fg).
  Proof.
    exact (pr2 SC x y z).
  Qed.

  (**
   3. Equivalence of enrichments with the elementary definition
   *)
  Section MakeStructEnrichment.
    Context (C : category)
            (SC : struct_enrichment C).

    Definition make_enrichment_over_struct_data
      : enrichment_data C (monoidal_cat_of_hset_struct P).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - exact (λ x y, _ ,, SC x y).
      - refine (λ x, (λ _, identity _) ,, _).
        abstract
          (cbn ;
           apply hset_struct_const).
      - simple refine (λ x y z, _ ,, _) ; cbn in *.
        + exact (λ fg, pr2 fg · pr1 fg).
        + apply struct_enrichment_comp.
      - refine (λ x y f, (λ _, f) ,, _).
        apply hset_struct_const.
      - exact (λ x y f, pr1 f tt).
    Defined.

    Proposition make_enrichment_over_struct_laws
      : enrichment_laws make_enrichment_over_struct_data.
    Proof.
      repeat split.
      - intros x y.
        use eq_mor_hset_struct.
        intro a ; cbn.
        rewrite id_right.
        apply idpath.
      - intros x y.
        use eq_mor_hset_struct.
        intro a ; cbn.
        rewrite id_left.
        apply idpath.
      - intros w x y z.
        use eq_mor_hset_struct.
        intro a ; cbn.
        rewrite assoc.
        apply idpath.
      - intros x y f.
        use eq_mor_hset_struct.
        intro a ; cbn in *.
        apply maponpaths.
        apply isapropunit.
    Qed.

    Definition make_enrichment_over_struct
      : enrichment C (monoidal_cat_of_hset_struct P)
      := make_enrichment_over_struct_data ,, make_enrichment_over_struct_laws.
  End MakeStructEnrichment.

  Section FromStructEnrichment.
    Context (C : category)
            (E : enrichment C (monoidal_cat_of_hset_struct P)).

    Definition mor_to_enriched_hom
               {x y : C}
               (f : x --> y)
      : pr11 (E ⦃ x , y ⦄)
      := pr1 (enriched_from_arr E f) tt.

    Definition enriched_hom_to_mor
               {x y : C}
               (f : pr11 (E ⦃ x , y ⦄))
      : x --> y.
    Proof.
      assert (mor_hset_struct P (hset_struct_unit P) (pr2 (E ⦃ x, y ⦄)) (λ _, f)) as H.
      {
        apply hset_struct_const.
      }
      exact (enriched_to_arr E (_ ,, H)).
    Defined.

    Definition mor_weq_enriched_hom
               (x y : C)
      : pr11 (E ⦃ x , y ⦄) ≃ (x --> y).
    Proof.
      use weq_iso.
      - exact enriched_hom_to_mor.
      - exact mor_to_enriched_hom.
      - abstract
          (intro f ;
           unfold mor_to_enriched_hom, enriched_hom_to_mor ;
           rewrite enriched_from_to_arr ;
           apply idpath).
      - abstract
          (intro f ;
           unfold mor_to_enriched_hom, enriched_hom_to_mor ;
           refine (_ @ enriched_to_from_arr E f) ;
           apply maponpaths ;
           use eq_mor_hset_struct ;
           intro t ; cbn ;
           apply maponpaths ;
           apply isapropunit).
    Defined.

    Definition make_struct_enrichment_data
      : struct_enrichment_data C.
    Proof.
      intros x y.
      refine (transportf_struct_weq P _ (pr2 (E ⦃ x , y ⦄))).
      exact (mor_weq_enriched_hom x y).
    Defined.

    Proposition make_struct_enrichment_laws
      : struct_enrichment_laws make_struct_enrichment_data.
    Proof.
      intros x y z.
      use (transportf_struct_mor_prod_via_eq P).
      - exact (pr1 (enriched_comp E x y z)).
      - exact (pr2 (enriched_comp E x y z)).
      - intros fg ; cbn.
        unfold enriched_hom_to_mor.
        rewrite (enriched_to_arr_comp E).
        apply maponpaths.
        use eq_mor_hset_struct.
        intro t ; induction t.
        apply idpath.
    Qed.

    Definition make_struct_enrichment
      : struct_enrichment C.
    Proof.
      simple refine (_ ,, _).
      - exact make_struct_enrichment_data.
      - exact make_struct_enrichment_laws.
    Defined.
  End FromStructEnrichment.

  Section EnrichmentEquiv.
    Context {C : category}
            (E : enrichment C (monoidal_cat_of_hset_struct P)).

    Definition enrichment_over_struct_weq_struct_enrichment_iso
               (x y : C)
      : @z_iso
          (category_of_hset_struct P)
          (homset x y ,, make_struct_enrichment_data C E x y)
          (E ⦃ x , y ⦄).
    Proof.
      use make_z_iso.
      - simple refine (_ ,, _).
        + exact (λ f, pr1 (enriched_from_arr E f) tt).
        + cbn.
          apply transportf_struct_weq_on_invweq.
      - simple refine (_ ,, _).
        + refine (λ f, enriched_to_arr E ((λ _, f) ,, _)).
          apply hset_struct_const.
        + cbn.
          apply transportf_struct_weq_on_weq.
      - split.
        + use eq_mor_hset_struct.
          intro w ; cbn.
          refine (_ @ enriched_to_from_arr E _).
          apply maponpaths.
          use eq_mor_hset_struct.
          intro t.
          cbn.
          apply maponpaths.
          apply isapropunit.
        + use eq_mor_hset_struct.
          intro f.
          cbn.
          rewrite enriched_from_to_arr.
          apply idpath.
    Defined.

    Definition enrichment_over_struct_weq_struct_enrichment_inv_1
      : make_enrichment_over_struct C (make_struct_enrichment C E) = E.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_enrichment_laws.
      }
      use (invweq (total2_paths_equiv _ _ _)).
      use (invmap (enrichment_data_hom_path _ _ _)).
      {
        exact (is_univalent_category_of_hset_struct P).
      }
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - exact enrichment_over_struct_weq_struct_enrichment_iso.
      - intro x.
        use eq_mor_hset_struct.
        intro t ; cbn.
        rewrite enriched_from_arr_id.
        apply maponpaths.
        apply isapropunit.
      - intros x y z.
        use eq_mor_hset_struct.
        intro t ; cbn.
        rewrite enriched_from_arr_comp ; cbn.
        apply idpath.
      - intros x y f.
        use eq_mor_hset_struct.
        intro t.
        cbn.
        apply maponpaths.
        apply isapropunit.
      - intros x y f.
        cbn.
        assert (mor_hset_struct
                  P
                  (hset_struct_unit P)
                  (make_struct_enrichment_data C E x y)
                  (λ _, pr1 f tt))
          as H.
        {
          apply hset_struct_const.
        }
        refine (!(enriched_to_from_arr E (pr1 f tt)) @ _).
        apply maponpaths.
        use eq_mor_hset_struct.
        intro t ; induction t.
        cbn.
        apply idpath.
    Defined.
  End EnrichmentEquiv.

  Proposition enrichment_over_struct_weq_struct_enrichment_inv_2
              {C : category}
              (E : struct_enrichment C)
    : make_struct_enrichment C (make_enrichment_over_struct C E) = E.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_struct_enrichment_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    simpl.
    unfold make_struct_enrichment_data.
    unfold make_enrichment_over_struct.
    simpl.
    unfold transportf_struct_weq.
    refine (_ @ idpath_transportf _ _).
    apply maponpaths_2.
    refine (_ @ univalence_hSet_idweq _).
    apply maponpaths.
    use subtypePath.
    {
      intro ; apply isapropisweq.
    }
    apply idpath.
  Qed.

  Definition enrichment_over_struct_weq_struct_enrichment
             (C : category)
    : enrichment C (monoidal_cat_of_hset_struct P) ≃ struct_enrichment C.
  Proof.
    use weq_iso.
    - exact (make_struct_enrichment C).
    - exact (make_enrichment_over_struct C).
    - apply enrichment_over_struct_weq_struct_enrichment_inv_1.
    - apply enrichment_over_struct_weq_struct_enrichment_inv_2.
  Defined.

  (**
   4. Elementary definition of functor enrichments over structures
   *)
  Definition functor_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : struct_enrichment C₁)
             (P₂ : struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
    : UU
    := ∏ (x y : C₁), mor_hset_struct P (P₁ x y) (P₂ (F x) (F y)) (λ f, #F f).

  (**
   5. Equivalence of functor enrichments with elementary definition
   *)
  Definition make_functor_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : struct_enrichment C₁)
             (P₂ : struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
             (HF : functor_enrichment
                     F
                     (make_enrichment_over_struct C₁ P₁)
                     (make_enrichment_over_struct C₂ P₂))
    : functor_struct_enrichment P₁ P₂ F.
  Proof.
    intros x y.
    refine (transportf
              _
              _
              (pr2 (HF x y))).
    use funextsec.
    intro f.
    pose (eqtohomot
            (maponpaths
               pr1
               (functor_enrichment_from_arr HF f))
            tt)
      as p.
    cbn in p.
    exact (!p).
  Qed.

  Definition make_functor_enrichment_over_struct
             {C₁ C₂ : category}
             (P₁ : struct_enrichment C₁)
             (P₂ : struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
             (HF : functor_struct_enrichment P₁ P₂ F)
    : functor_enrichment
        F
        (make_enrichment_over_struct C₁ P₁)
        (make_enrichment_over_struct C₂ P₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, (λ f, #F f) ,, HF x y).
    - repeat split.
      + abstract
          (intros x ;
           use eq_mor_hset_struct ;
           intro f ; cbn ;
           apply functor_id).
      + abstract
          (intros x y z ;
           use eq_mor_hset_struct ;
           intro f ; cbn ;
           apply functor_comp).
      + abstract
          (intros x y f ;
           use eq_mor_hset_struct ;
           intro w ; cbn ;
           apply idpath).
  Defined.

  Definition functor_enrichment_over_struct_weq_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : struct_enrichment C₁)
             (P₂ : struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
    : functor_enrichment
        F
        (make_enrichment_over_struct C₁ P₁)
        (make_enrichment_over_struct C₂ P₂)
      ≃
      functor_struct_enrichment P₁ P₂ F.
  Proof.
    use weq_iso.
    - exact (make_functor_struct_enrichment P₁ P₂ F).
    - exact (make_functor_enrichment_over_struct P₁ P₂ F).
    - abstract
        (intro EF ;
         use subtypePath ; [ intro ; apply isaprop_is_functor_enrichment | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         use eq_mor_hset_struct ;
         intro f ;
         cbn ;
         exact (eqtohomot (maponpaths pr1 (functor_enrichment_from_arr EF f)) tt)).
    - abstract
        (intros EF ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         cbn ;
         apply isaprop_hset_struct_on_mor).
  Defined.
End FixAStructure.
