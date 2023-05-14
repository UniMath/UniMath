(*****************************************************************

 Enrichments over smash products

 In this file, we characterize enrichments over structures with
 smash products in more elementary terms. The idea is the same as
 for cartesian structures (see StructureEnriched.v), but there is
 one difference. This difference is caused by the fact that the
 smash product is a quotient. As such, this must be taken into
 account, and thus we get an additional requirement. Since the
 structurs we enrich over, are pointed, every homset has a
 distinguished point, which we call the zero morphism. The
 additional requirement says that composition with a zero morphism
 again gives a zero morphism.

 Contents
 1. The monoidal category is faithful
 2. Elementary definition of enrichment over structures
 3. Equivalence between the two definitions of enrichments
 4. Elementary definition of functor enrichments over structures
 5. Equivalence between the two definition of  functor enrichments

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SmashProductMonoidal.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.

Local Open Scope cat.

Section FixAStructureWithSmash.
  Context (P : hset_struct_with_smash_closed).

  (**
   1. The monoidal category is faithful
   *)
  Definition category_of_smash_struct_faithful_moncat
    : faithful_moncat (smash_product_monoidal_cat P).
  Proof.
    intros R₁ R₂ f g p.
    use subtypePath.
    {
      intro ; cbn -[isaprop].
      apply isaprop_hset_struct_on_mor.
    }
    use funextsec ; intro x.
    assert (mor_hset_struct
              P
              (pr2 (monoidal_unit (smash_product_monoidal_cat P)))
              (pr2 R₁)
              (pointed_hset_struct_map_from_unit P (pr2 R₁) x)) as H.
    {
      apply hset_struct_with_smash_map_from_unit.
    }
    exact (eqtohomot (maponpaths pr1 (p (_ ,, H))) true).
  Qed.

  (**
   2. Elementary definition of enrichment over structures
   *)
  Definition smash_struct_enrichment_data
             (C : category)
    : UU
    := ∏ (x y : C), P (homset x y).

  Definition smash_struct_enrichment_point
             {C : category}
             (SC : smash_struct_enrichment_data C)
             (x y : C)
    : x --> y
    := hset_struct_point P (SC x y).

  Definition smash_struct_enrichment_laws
             {C : category}
             (SC : smash_struct_enrichment_data C)
    : UU
    := (∏ (x y z : C),
        mor_hset_struct
          P
          (hset_struct_prod P (SC y z) (SC x y))
          (SC x z)
          (λ (fg : C ⟦ y, z ⟧ × C ⟦ x, y ⟧), pr2 fg · pr1 fg))
       ×
       (∏ (x y z : C)
          (f : x --> y),
        f · smash_struct_enrichment_point SC y z
        =
        smash_struct_enrichment_point SC x z)
       ×
       (∏ (x y z : C)
          (f : y --> z),
        smash_struct_enrichment_point SC x y · f
        =
        smash_struct_enrichment_point SC x z).

  Proposition isaprop_smash_struct_enrichment_laws
              {C : category}
              (SC : smash_struct_enrichment_data C)
    : isaprop (smash_struct_enrichment_laws SC).
  Proof.
    repeat (use isapropdirprod) ; repeat (use impred ; intro).
    - apply isaprop_hset_struct_on_mor.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition smash_struct_enrichment
             (C : category)
    : UU
    := ∑ (SC : smash_struct_enrichment_data C),
       smash_struct_enrichment_laws SC.

  Definition smash_struct_enrichment_to_data
             {C : category}
             (SC : smash_struct_enrichment C)
             (x y : C)
    : P (homset x y)
    := pr1 SC x y.

  Coercion smash_struct_enrichment_to_data : smash_struct_enrichment >-> Funclass.

  Proposition smash_struct_enrichment_comp
              {C : category}
              (SC : smash_struct_enrichment C)
              (x y z : C)
    : mor_hset_struct
        P
        (hset_struct_prod P (SC y z) (SC x y))
        (SC x z)
        (λ (fg : C ⟦ y, z ⟧ × C ⟦ x, y ⟧), pr2 fg · pr1 fg).
  Proof.
    exact (pr12 SC x y z).
  Qed.

  Proposition smash_struct_enrichment_comp_point_l
              {C : category}
              (SC : smash_struct_enrichment C)
              (x y z : C)
              (f : x --> y)
    : f · smash_struct_enrichment_point SC y z
      =
      smash_struct_enrichment_point SC x z.
  Proof.
    exact (pr122 SC x y z f).
  Qed.

  Proposition smash_struct_enrichment_comp_point_r
              {C : category}
              (SC : smash_struct_enrichment C)
              (x y z : C)
              (f : y --> z)
    : smash_struct_enrichment_point SC x y · f
      =
      smash_struct_enrichment_point SC x z.
  Proof.
    exact (pr222 SC x y z f).
  Qed.

  (**
   3. Equivalence between the two definitions of enrichments
   *)
  Section MakeSmashStructEnrichment.
    Context (C : category)
            (SC : smash_struct_enrichment C).

    Definition smash_struct_comp
               {x y z : C}
      : setquot (smash_eqrel (pr1 P) (pr12 P) (SC y z) (SC x y)) → homset x z.
    Proof.
      use map_from_smash.
      - exact (λ f g, g · f).
      - abstract
          (intros f₁ f₂ ; cbn ;
           rewrite !(smash_struct_enrichment_comp_point_l SC) ;
           apply idpath).
      - abstract
          (intros g f ; cbn ;
           rewrite !(smash_struct_enrichment_comp_point_l SC) ;
           rewrite !(smash_struct_enrichment_comp_point_r SC) ;
           apply idpath).
      - abstract
          (intros g₁ g₂ ; cbn ;
           rewrite !(smash_struct_enrichment_comp_point_r SC) ;
           apply idpath).
    Defined.

    Definition make_enrichment_over_smash_struct_data
      : enrichment_data C (smash_product_monoidal_cat P).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _).
      - exact (λ x y, _ ,, SC x y).
      - refine (λ x, pointed_hset_struct_map_from_unit P (SC x x) (identity _) ,, _).
        abstract
          (cbn ;
           apply hset_struct_with_smash_map_from_unit).
      - simple refine (λ x y z, _ ,, _).
        + exact smash_struct_comp.
        + use hset_struct_with_smash_map_from_smash.
          apply smash_struct_enrichment_comp.
      - refine (λ x y f, pointed_hset_struct_map_from_unit P (SC x y) f ,, _).
        abstract
          (cbn ;
           apply hset_struct_with_smash_map_from_unit).
      - exact (λ x y f, pr1 f true).
    Defined.

    Proposition make_enrichment_over_smash_struct_laws
      : enrichment_laws make_enrichment_over_smash_struct_data.
    Proof.
      repeat split.
      - intros x y.
        use eq_mor_hset_struct.
        use setquotunivprop' ; [ intro ; apply homset_property | ].
        intro a.
        induction a as [ b f ].
        induction b ; cbn in *.
        + rewrite id_right.
          apply idpath.
        + rewrite (smash_struct_enrichment_comp_point_l SC).
          apply idpath.
      - intros x y.
        use eq_mor_hset_struct.
        use setquotunivprop' ; [ intro ; apply homset_property | ].
        intro a.
        induction a as [ f b ].
        induction b ; cbn in *.
        + rewrite id_left.
          apply idpath.
        + rewrite (smash_struct_enrichment_comp_point_r SC).
          apply idpath.
      - intros w x y z.
        use eq_mor_hset_struct.
        use setquotunivprop' ; [ intro ; apply homset_property | ].
        intro a.
        induction a as [ a h ].
        revert a.
        use setquotunivprop' ; [ intro ; apply homset_property | ].
        intro a.
        induction a as [ f g ] ; cbn in *.
        rewrite assoc.
        apply idpath.
      - intros x y f.
        use eq_mor_hset_struct.
        intro a.
        induction a ; cbn.
        + apply idpath.
        + rewrite <- (pointed_hset_struct_preserve_point
                        _
                        (pr2 f)).
          apply maponpaths.
          apply hset_struct_with_smash_point_unit.
    Qed.

    Definition make_enrichment_over_smash_struct
      : enrichment C (smash_product_monoidal_cat P)
      := make_enrichment_over_smash_struct_data
         ,,
         make_enrichment_over_smash_struct_laws.
  End MakeSmashStructEnrichment.

  Section FromStructSmashEnrichment.
    Context (C : category)
            (E : enrichment C (smash_product_monoidal_cat P)).

    Definition mor_to_enriched_smash_hom
               {x y : C}
               (f : x --> y)
      : pr11 (E ⦃ x , y ⦄)
      := pr1 (enriched_from_arr E f) true.

    Definition enriched_smash_hom_to_mor
               {x y : C}
               (f : pr11 (E ⦃ x , y ⦄))
      : x --> y.
    Proof.
      assert (mor_hset_struct
                P
                (pr2 (monoidal_unit (smash_product_monoidal_cat P)))
                (pr2 (E ⦃ x , y ⦄))
                (pointed_hset_struct_map_from_unit
                   P
                   (pr2 (E ⦃ x , y ⦄))
                   f))
        as H.
      {
        apply hset_struct_with_smash_map_from_unit.
      }
      exact (enriched_to_arr E (_ ,, H)).
    Defined.

    Definition mor_weq_enriched_smash_hom
               (x y : C)
      : pr11 (E ⦃ x , y ⦄) ≃ (x --> y).
    Proof.
      use weq_iso.
      - exact enriched_smash_hom_to_mor.
      - exact mor_to_enriched_smash_hom.
      - abstract
          (intro f ;
           unfold mor_to_enriched_smash_hom, enriched_smash_hom_to_mor ;
           rewrite enriched_from_to_arr ;
           apply idpath).
      - abstract
          (intro f ;
           unfold mor_to_enriched_smash_hom, enriched_smash_hom_to_mor ;
           refine (_ @ enriched_to_from_arr E f) ;
           apply maponpaths ;
           use eq_mor_hset_struct ;
           intro b ; cbn ;
           induction b ; [ apply idpath | ] ; cbn ;
           rewrite <- (pointed_hset_struct_preserve_point
                         _
                         (pr2 (enriched_from_arr E f))) ;
           apply maponpaths ;
           apply hset_struct_with_smash_point_unit).
    Defined.

    Definition make_smash_struct_enrichment_data
      : smash_struct_enrichment_data C.
    Proof.
      intros x y.
      refine (transportf_struct_weq P _ (pr2 (E ⦃ x , y ⦄))).
      exact (mor_weq_enriched_smash_hom x y).
    Defined.

    Proposition enriched_from_arr_smash_lemma
                (x y : C)
      : pr1 (enriched_from_arr
               E
               (hset_struct_point P (make_smash_struct_enrichment_data x y)))
          true
        =
        hset_struct_point P (pr2 (E ⦃ x, y ⦄)).
    Proof.
      assert (mor_hset_struct
                P
                (pr2 (monoidal_unit (smash_product_monoidal_cat P)))
                (pr2 (E ⦃ x, y ⦄))
                (pointed_hset_struct_map_from_unit
                   P
                   (pr2 (E ⦃ x, y ⦄))
                   (hset_struct_point P (pr2 (E ⦃ x, y ⦄)))))
        as H.
      {
        apply hset_struct_with_smash_map_from_unit.
      }
      refine (_ @ maponpaths (λ z, pr1 z true) (enriched_from_to_arr E (_ ,, H))).
      apply maponpaths_2.
      apply maponpaths.
      unfold make_smash_struct_enrichment_data.
      unfold transportf_struct_weq.
      rewrite transportf_hset_struct_point.
      cbn ; unfold enriched_smash_hom_to_mor.
      apply maponpaths.
      use eq_mor_hset_struct.
      intro ; cbn.
      apply idpath.
    Qed.

    Proposition make_smash_struct_enrichment_laws
      : smash_struct_enrichment_laws make_smash_struct_enrichment_data.
    Proof.
      repeat split.
      - intros x y z.
        use (transportf_struct_mor_prod_via_eq P).
        + exact (λ fg, pr1 (enriched_comp E x y z) (setquotpr _ fg)).
        + abstract
            (refine (hset_struct_comp P _ (pr2 (enriched_comp E x y z))) ;
             apply hset_struct_with_smash_setquotpr).
        + intros fg ; cbn.
          unfold enriched_smash_hom_to_mor.
          rewrite (enriched_to_arr_comp E).
          apply maponpaths.
          use eq_mor_hset_struct.
          intro b ; induction b ; cbn.
          * apply idpath.
          * pose (pointed_hset_struct_preserve_point
                    P
                    (pr2 (enriched_comp E x y z)))
              as p.
            refine (_ @ p).
            apply maponpaths.
            refine (_ @ !(hset_struct_with_smash_point_smash _ _ _)).
            use iscompsetquotpr.
            apply hinhpr.
            use inr.
            split ; unfold product_point_coordinate.
            ** use inr.
               cbn.
               rewrite <- (pointed_hset_struct_preserve_point
                         _
                         (pr2 (enriched_from_arr E (pr2 fg)))).
               apply maponpaths.
               refine (!_).
               apply hset_struct_with_smash_point_unit.
            ** use inl.
               apply idpath.
      - intros x y z f.
        unfold smash_struct_enrichment_point.
        refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
        apply maponpaths.
        rewrite enriched_from_arr_comp.
        use subtypePath.
        {
          intro ; cbn -[isaprop].
          apply isaprop_hset_struct_on_mor.
        }
        use funextsec ; intro a.
        cbn.
        induction a ; cbn.
        + rewrite !enriched_from_arr_smash_lemma.
          pose (pointed_hset_struct_preserve_point
                  P
                  (pr2 (enriched_comp E x y z)))
            as p.
          refine (_ @ p).
          apply maponpaths.
          refine (_ @ !(hset_struct_with_smash_point_smash _ _ _)).
          use iscompsetquotpr.
          apply hinhpr.
          use inr.
          split ; unfold product_point_coordinate.
          * use inl.
            apply idpath.
          * use inl.
            apply idpath.
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            exact (!(hset_struct_with_smash_point_unit (pr122 P))).
          }
          refine (pointed_hset_struct_preserve_point
                    _
                    (pr2 (enriched_from_arr E _))
                  @ _).
          refine (!_).
          pose (pointed_hset_struct_preserve_point
                  P
                  (pr2 (enriched_comp E x y z)))
            as p.
          refine (_ @ p).
          apply maponpaths.
          refine (_ @ !(hset_struct_with_smash_point_smash _ _ _)).
          use iscompsetquotpr.
          apply hinhpr.
          use inr.
          split ; unfold product_point_coordinate.
          * use inr.
            cbn.
            rewrite <- (pointed_hset_struct_preserve_point
                          _
                          (pr2 (enriched_from_arr E f))).
            apply maponpaths.
            refine (!_).
            apply hset_struct_with_smash_point_unit.
          * use inl.
            apply idpath.
      - intros x y z f.
        unfold smash_struct_enrichment_point.
        refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
        apply maponpaths.
        rewrite enriched_from_arr_comp.
        use subtypePath.
        {
          intro ; cbn -[isaprop].
          apply isaprop_hset_struct_on_mor.
        }
        use funextsec ; intro a.
        cbn.
        induction a ; cbn.
        + rewrite !enriched_from_arr_smash_lemma.
          pose (pointed_hset_struct_preserve_point
                  P
                  (pr2 (enriched_comp E x y z)))
            as p.
          refine (_ @ p).
          apply maponpaths.
          refine (_ @ !(hset_struct_with_smash_point_smash _ _ _)).
          use iscompsetquotpr.
          apply hinhpr.
          use inr.
          split ; unfold product_point_coordinate.
          * use inr.
            apply idpath.
          * use inl.
            apply idpath.
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            exact (!(hset_struct_with_smash_point_unit (pr122 P))).
          }
          refine (pointed_hset_struct_preserve_point
                    _
                    (pr2 (enriched_from_arr E _))
                  @ _).
          refine (!_).
          pose (pointed_hset_struct_preserve_point
                  P
                  (pr2 (enriched_comp E x y z)))
            as p.
          refine (_ @ p).
          apply maponpaths.
          refine (_ @ !(hset_struct_with_smash_point_smash _ _ _)).
          use iscompsetquotpr.
          apply hinhpr.
          use inr.
          split ; unfold product_point_coordinate.
          * use inr.
            cbn.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (hset_struct_with_smash_point_unit (pr122 P)).
            }
            exact (pointed_hset_struct_preserve_point
                     _
                     (pr2 (enriched_from_arr E _))).
          * use inl.
            apply idpath.
    Qed.

    Definition make_smash_struct_enrichment
      : smash_struct_enrichment C.
    Proof.
      simple refine (_ ,, _).
      - exact make_smash_struct_enrichment_data.
      - exact make_smash_struct_enrichment_laws.
    Defined.
  End FromStructSmashEnrichment.

  Section SmashEnrichmentEquiv.
    Context {C : category}
            (E : enrichment C (smash_product_monoidal_cat P)).

    Definition enrichment_over_smash_struct_weq_struct_enrichment_iso
               (x y : C)
      : @z_iso
          (category_of_hset_struct P)
          (homset x y ,, make_smash_struct_enrichment_data C E x y)
          (E ⦃ x , y ⦄).
    Proof.
      use make_z_iso.
      - simple refine (_ ,, _).
        + exact (λ f, pr1 (enriched_from_arr E f) true).
        + cbn.
          apply transportf_struct_weq_on_invweq.
      - simple refine (_ ,, _).
        + refine (λ f, enriched_to_arr
                         E
                         (pointed_hset_struct_map_from_unit P (pr2 (E ⦃ x, y ⦄)) f
                          ,,
                          _)).
          apply hset_struct_with_smash_map_from_unit.
        + cbn.
          apply transportf_struct_weq_on_weq.
      - split.
        + use eq_mor_hset_struct.
          intro w ; cbn.
          refine (_ @ enriched_to_from_arr E _).
          apply maponpaths.
          use eq_mor_hset_struct.
          intro b.
          induction b ; cbn.
          * apply idpath.
          * refine (!(pointed_hset_struct_preserve_point
                        P
                        (pr2 (enriched_from_arr E w))) @ _).
            apply maponpaths.
            apply hset_struct_with_smash_point_unit.
        + use eq_mor_hset_struct.
          intro f.
          cbn.
          rewrite enriched_from_to_arr.
          apply idpath.
    Defined.

    Definition enrichment_over_smash_struct_weq_smash_struct_enrichment_inv_1
      : make_enrichment_over_smash_struct C (make_smash_struct_enrichment C E) = E.
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
      - exact enrichment_over_smash_struct_weq_struct_enrichment_iso.
      - intro x.
        use eq_mor_hset_struct.
        intro b.
        induction b ; cbn.
        + rewrite enriched_from_arr_id.
          apply idpath.
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (hset_struct_with_smash_point_unit (pr122 P)).
          }
          refine (pointed_hset_struct_preserve_point
                    P
                    (pr2 (enriched_id E x))
                  @ _).
          refine (!_).
          apply enriched_from_arr_smash_lemma.
      - intros x y z.
        use eq_mor_hset_struct.
        use setquotunivprop'.
        {
          intro.
          apply setproperty.
        }
        intros fg ; cbn ; cbn in fg.
        induction fg as [ f g ].
        rewrite enriched_from_arr_comp ; cbn.
        apply idpath.
      - intros x y f.
        use eq_mor_hset_struct.
        intro b.
        induction b ; cbn.
        + apply idpath.
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (hset_struct_with_smash_point_unit (pr122 P)).
          }
          refine (pointed_hset_struct_preserve_point
                    P
                    (pr2 (enriched_from_arr E f))
                  @ _).
          refine (!_).
          apply enriched_from_arr_smash_lemma.
      - intros x y f.
        refine (!(enriched_to_from_arr E (pr1 f true)) @ _).
        apply maponpaths.
        use eq_mor_hset_struct.
        intro b ; induction b.
        + cbn.
          apply idpath.
        + cbn.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (hset_struct_with_smash_point_unit (pr122 P)).
          }
          refine (pointed_hset_struct_preserve_point
                    P
                    (pr2 (enriched_from_arr E _))
                  @ _).
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply (hset_struct_with_smash_point_unit (pr122 P)).
            }
            exact (pointed_hset_struct_preserve_point P (pr2 f)).
          }
          cbn.
          apply enriched_from_arr_smash_lemma.
    Qed.
  End SmashEnrichmentEquiv.

  Proposition enrichment_over_smash_struct_weq_smash_struct_enrichment_inv_2
              {C : category}
              (E : smash_struct_enrichment C)
    : make_smash_struct_enrichment C (make_enrichment_over_smash_struct C E) = E.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_smash_struct_enrichment_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    simpl.
    unfold make_smash_struct_enrichment_data.
    unfold make_enrichment_over_smash_struct.
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

  Definition enrichment_over_smash_struct_weq_smash_struct_enrichment
             (C : category)
    : enrichment C (smash_product_monoidal_cat P) ≃ smash_struct_enrichment C.
  Proof.
    use weq_iso.
    - exact (make_smash_struct_enrichment C).
    - exact (make_enrichment_over_smash_struct C).
    - apply enrichment_over_smash_struct_weq_smash_struct_enrichment_inv_1.
    - apply enrichment_over_smash_struct_weq_smash_struct_enrichment_inv_2.
  Defined.

  (**
   4. Elementary definition of functor enrichments over structures
   *)
  Definition functor_smash_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : smash_struct_enrichment C₁)
             (P₂ : smash_struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
    : UU
    := ∏ (x y : C₁), mor_hset_struct P (P₁ x y) (P₂ (F x) (F y)) (λ f, #F f).

  (**
   5. Equivalence between the two definition of  functor enrichments
   *)
  Definition make_functor_smash_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : smash_struct_enrichment C₁)
             (P₂ : smash_struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
             (HF : functor_enrichment
                     F
                     (make_enrichment_over_smash_struct C₁ P₁)
                     (make_enrichment_over_smash_struct C₂ P₂))
    : functor_smash_struct_enrichment P₁ P₂ F.
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
            true)
      as p.
    cbn in p.
    exact (!p).
  Qed.

  Definition make_functor_enrichment_over_smash_struct
             {C₁ C₂ : category}
             (P₁ : smash_struct_enrichment C₁)
             (P₂ : smash_struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
             (HF : functor_smash_struct_enrichment P₁ P₂ F)
    : functor_enrichment
        F
        (make_enrichment_over_smash_struct C₁ P₁)
        (make_enrichment_over_smash_struct C₂ P₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, (λ f, #F f) ,, HF x y).
    - repeat split.
      + abstract
          (intros x ;
           use eq_mor_hset_struct ;
           intro b ; induction b ; cbn ; [ apply functor_id | ] ;
           exact (pointed_hset_struct_preserve_point _ (HF x x))).
      + abstract
          (intros x y z ;
           use eq_mor_hset_struct ;
           use setquotunivprop' ; [ intro ; apply homset_property | ] ;
           intros fg ;
           induction fg as [ f g ] ;
           apply functor_comp).
      + abstract
          (intros x y f ;
           use eq_mor_hset_struct ;
           intro b ; induction b ; cbn ; [ apply idpath | ] ;
           refine (!_) ;
           apply (pointed_hset_struct_preserve_point _ (HF x y))).
  Defined.

  Definition functor_enrichment_over_smash_struct_weq_smash_struct_enrichment
             {C₁ C₂ : category}
             (P₁ : smash_struct_enrichment C₁)
             (P₂ : smash_struct_enrichment C₂)
             (F : C₁ ⟶ C₂)
    : functor_enrichment
        F
        (make_enrichment_over_smash_struct C₁ P₁)
        (make_enrichment_over_smash_struct C₂ P₂)
      ≃
      functor_smash_struct_enrichment P₁ P₂ F.
  Proof.
    use weq_iso.
    - exact (make_functor_smash_struct_enrichment P₁ P₂ F).
    - exact (make_functor_enrichment_over_smash_struct P₁ P₂ F).
    - abstract
        (intro EF ;
         use subtypePath ; [ intro ; apply isaprop_is_functor_enrichment | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         use eq_mor_hset_struct ;
         intro f ;
         cbn ;
         exact (eqtohomot (maponpaths pr1 (functor_enrichment_from_arr EF f)) true)).
    - abstract
        (intros EF ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         cbn ;
         apply isaprop_hset_struct_on_mor).
  Defined.
End FixAStructureWithSmash.
