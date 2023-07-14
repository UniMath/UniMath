(**********************************************************************

 Categories enriched over posets

 In this file, we study categories enriched over posets. We provide
 an elementary definition for both enrichments of categories and of
 functors and we prove the equivalence of these notions with the
 general notion of enrichments via the cartesian monoidal category of
 posets.

 Enrichments of posets for categories means that every hom-set is
 equipped with the structure of a poset and that composition is
 monotone, while enrichment for functors means that the action on
 morphisms is monotone.

 Contents
 1. The monoidal category is faithful
 2. Elementary definition of poset enrichments
 3. Equivalence of enrichments with the elementary definition
 4. Elementary definition of poset enriched functors
 5. Equivalence of functor enrichments with elementary definition

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.PosetsMonoidal.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.

Local Open Scope cat.

(**
 1. The monoidal category is faithful
 *)
Definition poset_faithful_moncat
  : faithful_moncat poset_monoidal_cat.
Proof.
  intros R₁ R₂ f g p.
  use eq_monotone_function.
  intro x.
  assert (is_monotone unit_PartialOrder (pr2 R₁) (λ _, x)) as H.
  {
    intros w₁ w₂ q.
    apply refl_PartialOrder.
  }
  exact (eqtohomot (maponpaths pr1 (p ((λ _, x) ,, H))) tt).
Qed.

(**
 2. Elementary definition of poset enrichments
 *)
Definition poset_enrichment_data
           (C : category)
  : UU
  := ∏ (x y : C), PartialOrder (homset x y).

Definition poset_enrichment_laws
           {C : category}
           (PEC : poset_enrichment_data C)
  : UU
  := (∏ (x y z : C)
        (f₁ f₂ : x --> y)
        (g : y --> z)
        (p : PEC x y f₁ f₂),
      PEC x z (f₁ · g) (f₂ · g))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g₁ g₂ : y --> z)
        (p : PEC y z g₁ g₂),
      PEC x z (f · g₁) (f · g₂)).

Proposition isaprop_poset_enrichment_laws
            {C : category}
            (PEC : poset_enrichment_data C)
  : isaprop (poset_enrichment_laws PEC).
Proof.
  use isapropdirprod ; (repeat (use impred ; intro)) ; apply propproperty.
Qed.

Definition poset_enrichment
           (C : category)
  : UU
  := ∑ (PEC : poset_enrichment_data C), poset_enrichment_laws PEC.

Definition poset_enrichment_hom_poset
           {C : category}
           (PEC : poset_enrichment C)
           (x y : C)
  : PartialOrder (x --> y ,, homset_property C x y)
  := pr1 PEC x y.

Coercion poset_enrichment_hom_poset : poset_enrichment >-> Funclass.

Proposition poset_enrichment_comp_l
            {C : category}
            (PEC : poset_enrichment C)
            {x y z : C}
            {f₁ f₂ : x --> y}
            (g : y --> z)
            (p : PEC x y f₁ f₂)
  : PEC x z (f₁ · g) (f₂ · g).
Proof.
  exact (pr12 PEC x y z f₁ f₂ g p).
Qed.

Proposition poset_enrichment_comp_r
            {C : category}
            (PEC : poset_enrichment C)
            {x y z : C}
            (f : x --> y)
            {g₁ g₂ : y --> z}
            (p : PEC y z g₁ g₂)
  : PEC x z (f · g₁) (f · g₂).
Proof.
  exact (pr22 PEC x y z f g₁ g₂ p).
Qed.

(**
 3. Equivalence of enrichments with the elementary definition
 *)
Section MakePosetEnrichment.
  Context (C : category)
          (PEC : poset_enrichment C).

  Definition make_enrichment_over_poset_data
    : enrichment_data C poset_monoidal_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, _ ,, PEC x y).
    - refine (λ x, (λ _, identity _) ,, _).
      abstract
        (cbn ; intros t₁ t₂ p ;
         apply refl_PartialOrder).
    - simple refine (λ x y z, _ ,, _) ; cbn in *.
      + exact (λ fg, pr2 fg · pr1 fg).
      + abstract
          (intros fg₁ fg₂ p ; cbn in * ;
           exact (trans_PartialOrder
                    _
                    (poset_enrichment_comp_l PEC _ (pr2 p))
                    (poset_enrichment_comp_r PEC _ (pr1 p)))).
    - refine (λ x y f, (λ _, f) ,, _).
      abstract
        (intros t₁ t₂ p ; cbn in * ;
         apply refl_PartialOrder).
    - exact (λ x y f, pr1 f tt).
  Defined.

  Proposition make_enrichment_over_poset_laws
    : enrichment_laws make_enrichment_over_poset_data.
  Proof.
    repeat split.
    - intros x y.
      use eq_monotone_function.
      intro a ; cbn.
      rewrite id_right.
      apply idpath.
    - intros x y.
      use eq_monotone_function.
      intro a ; cbn.
      rewrite id_left.
      apply idpath.
    - intros w x y z.
      use eq_monotone_function.
      intro a ; cbn.
      rewrite assoc.
      apply idpath.
    - intros x y f.
      use eq_monotone_function.
      intro a ; cbn in *.
      apply maponpaths.
      apply isapropunit.
  Qed.

  Definition make_enrichment_over_poset
    : enrichment C poset_monoidal_cat
    := make_enrichment_over_poset_data ,, make_enrichment_over_poset_laws.
End MakePosetEnrichment.

Section FromPosetEnrichment.
  Context (C : category)
          (E : enrichment C poset_monoidal_cat).

  Definition make_poset_enrichment_rel
             (x y : C)
    : hrel (x --> y).
  Proof.
    refine (λ f g, _).
    use make_hProp.
    - exact (pr12 (E ⦃ x , y ⦄)
                  (pr1 (enriched_from_arr E f) tt)
                  (pr1 (enriched_from_arr E g) tt)).
    - apply (pr12 (E ⦃ x , y ⦄)).
  Defined.

  Definition make_poset_enrichment_data
    : poset_enrichment_data C.
  Proof.
    intros x y.
    simple refine (_ ,, ((_ ,, _) ,, _)).
    - exact (make_poset_enrichment_rel x y).
    - intros f g h p q.
      exact (trans_PartialOrder (pr2 (E ⦃ x , y ⦄)) p q).
    - intros f.
      exact (refl_PartialOrder (pr2 (E ⦃ x , y ⦄)) _).
    - cbn.
      intros f g p q.
      rewrite <- (enriched_to_from_arr E f).
      rewrite <- (enriched_to_from_arr E g).
      apply maponpaths.
      use eq_monotone_function.
      intro w.
      induction w.
      exact (antisymm_PartialOrder (pr2 (E ⦃ x , y ⦄)) p q).
  Defined.

  Proposition make_poset_enrichment_laws
    : poset_enrichment_laws make_poset_enrichment_data.
  Proof.
    repeat split.
    - intros x y z f₁ f₂ g p ; cbn.
      rewrite !enriched_from_arr_comp ; cbn.
      pose (Ef₁ := enriched_from_arr E f₁ : monotone_function _ _).
      pose (Ef₂ := enriched_from_arr E f₂ : monotone_function _ _).
      pose (Eg := enriched_from_arr E g : monotone_function _ _).
      use (pr2 (enriched_comp E x y z) (Eg tt ,, Ef₁ tt) (Eg tt ,, Ef₂ tt)).
      split.
      + apply refl_PartialOrder.
      + exact p.
    - intros x y z f g₁ g₂ p ;cbn.
      rewrite !enriched_from_arr_comp ; cbn.
      pose (Ef := enriched_from_arr E f : monotone_function _ _).
      pose (Eg₁ := enriched_from_arr E g₁ : monotone_function _ _).
      pose (Eg₂ := enriched_from_arr E g₂ : monotone_function _ _).
      use (pr2 (enriched_comp E x y z) (Eg₁ tt ,, Ef tt) (Eg₂ tt ,, Ef tt)).
      split.
      + exact p.
      + apply refl_PartialOrder.
  Qed.

  Definition make_poset_enrichment
    : poset_enrichment C
    := make_poset_enrichment_data ,, make_poset_enrichment_laws.
End FromPosetEnrichment.

Section EnrichmentOverPosetInverse.
  Context {C : category}
          (E : enrichment C poset_monoidal_cat).

  Definition enrichment_over_poset_weq_poset_enrichment_inv_iso
             (x y : C)
    : z_iso
        ((pr11 (make_enrichment_over_poset C (make_poset_enrichment C E))) x y)
        (E ⦃ x , y ⦄).
  Proof.
    use make_z_iso ; cbn.
    - simple refine (_ ,, _).
      + exact (λ f, pr1 (enriched_from_arr E f) tt).
      + abstract
          (cbn ;
           intros f g p ;
           apply p).
    - simple refine (_ ,, _).
      + refine (λ f, enriched_to_arr E _).
        simple refine (_ ,, _).
        * exact (λ _, f).
        * abstract
            (cbn ;
             intros t₁ t₂ p ;
             apply refl_PartialOrder).
      + abstract
          (intros f₁ f₂ p ; cbn ;
           rewrite !enriched_from_to_arr ; cbn ;
           exact p).
    - split.
      + abstract
          (use eq_monotone_function ;
           intro f ; cbn in * ;
           refine (_ @ enriched_to_from_arr E f) ;
           apply maponpaths ;
           use eq_monotone_function ;
           intro t ; cbn ;
           apply maponpaths ;
           apply isapropunit).
      + abstract
          (use eq_monotone_function ;
           intro f ; cbn in * ;
           assert (is_monotone unit_PartialOrder (pr2 (E ⦃ x, y ⦄)) (λ _ : unit, f)) as H ;
           [ intros t₁ t₂ p ;
             apply refl_PartialOrder
           | ] ;
           refine (_ @ eqtohomot (maponpaths pr1 (enriched_from_to_arr E (_ ,, H))) tt) ;
           cbn ;
           apply maponpaths_2 ;
           do 3 apply maponpaths ;
           apply isaprop_is_monotone).
  Defined.

  Definition enrichment_over_poset_weq_poset_enrichment_inv_1
    : make_enrichment_over_poset C (make_poset_enrichment C E) = E.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enrichment_laws.
    }
    use (invweq (total2_paths_equiv _ _ _)).
    use (invmap (enrichment_data_hom_path _ _ _)).
    {
      exact is_univalent_category_of_posets.
    }
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact enrichment_over_poset_weq_poset_enrichment_inv_iso.
    - abstract
        (intro x ;
         use eq_monotone_function ;
         intro w ; cbn ;
         rewrite enriched_from_arr_id ;
         apply maponpaths ;
         apply isapropunit).
    - abstract
        (intros x y z ;
         use eq_monotone_function ;
         intro w ; cbn ;
         rewrite enriched_from_arr_comp ; cbn ;
         apply idpath).
    - abstract
        (intros x y f ;
         use eq_monotone_function ;
         intro w ; cbn ;
         apply maponpaths ;
         apply isapropunit).
    - abstract
        (intros x y f ;
         cbn ;
         refine (!_) ;
         refine (_ @ enriched_to_from_arr E (pr1 f tt)) ;
         apply maponpaths ;
         use eq_monotone_function ;
         intro w ; cbn ;
         induction w ;
         apply idpath).
  Defined.
End EnrichmentOverPosetInverse.

Definition enrichment_over_poset_weq_poset_enrichment_inv_2
           {C : category}
           (E : poset_enrichment C)
  : make_poset_enrichment C (make_enrichment_over_poset C E) = E.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_poset_enrichment_laws.
  }
  use funextsec ; intro x.
  use funextsec ; intro y.
  use subtypePath.
  {
    intro.
    apply isaprop_isPartialOrder.
  }
  apply idpath.
Qed.

Definition enrichment_over_poset_weq_poset_enrichment
           (C : category)
  : enrichment C poset_monoidal_cat ≃ poset_enrichment C.
Proof.
  use weq_iso.
  - exact (make_poset_enrichment C).
  - exact (make_enrichment_over_poset C).
  - exact enrichment_over_poset_weq_poset_enrichment_inv_1.
  - exact enrichment_over_poset_weq_poset_enrichment_inv_2.
Defined.

(**
 4. Elementary definition of poset enriched functors
 *)
Definition functor_poset_enrichment
           {C₁ C₂ : category}
           (P₁ : poset_enrichment C₁)
           (P₂ : poset_enrichment C₂)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁)
       (f g : x --> y),
     P₁ x y f g → P₂ (F x) (F y) (#F f) (#F g).

(**
 5. Equivalence of functor enrichments with elementary definition
 *)
Definition make_functor_poset_enrichment
           {C₁ C₂ : category}
           (P₁ : poset_enrichment C₁)
           (P₂ : poset_enrichment C₂)
           (F : C₁ ⟶ C₂)
           (HF : functor_enrichment
                   F
                   (make_enrichment_over_poset C₁ P₁)
                   (make_enrichment_over_poset C₂ P₂))
  : functor_poset_enrichment P₁ P₂ F.
Proof.
  intros x y f g p.
  pose (eqtohomot (maponpaths pr1 (functor_enrichment_from_arr HF f)) tt) as pf.
  pose (eqtohomot (maponpaths pr1 (functor_enrichment_from_arr HF g)) tt) as pg.
  cbn in pf, pg.
  rewrite pf, pg.
  exact (pr2 (HF x y) f g p).
Qed.

Definition make_functor_enrichment_over_poset
           {C₁ C₂ : category}
           (P₁ : poset_enrichment C₁)
           (P₂ : poset_enrichment C₂)
           (F : C₁ ⟶ C₂)
           (HF : functor_poset_enrichment P₁ P₂ F)
  : functor_enrichment
      F
      (make_enrichment_over_poset C₁ P₁)
      (make_enrichment_over_poset C₂ P₂).
Proof.
  simple refine (_ ,, _).
  - refine (λ x y, (λ f, #F f) ,, λ f g p, _).
    exact (HF x y f g p).
  - repeat split.
    + abstract
        (intros x ;
         use eq_monotone_function ;
         intro w ; cbn ;
         apply functor_id).
    + abstract
        (intros x y z ;
         use eq_monotone_function ;
         intro w ; cbn ;
         apply functor_comp).
    + abstract
        (intros x y z ;
         use eq_monotone_function ;
         intro w ; cbn ;
         apply idpath).
Defined.

Definition functor_enrichment_over_poset_weq_poset_enrichment
           {C₁ C₂ : category}
           (P₁ : poset_enrichment C₁)
           (P₂ : poset_enrichment C₂)
           (F : C₁ ⟶ C₂)
  : functor_enrichment
      F
      (make_enrichment_over_poset C₁ P₁)
      (make_enrichment_over_poset C₂ P₂)
    ≃
    functor_poset_enrichment P₁ P₂ F.
Proof.
  use weq_iso.
  - exact (make_functor_poset_enrichment P₁ P₂ F).
  - exact (make_functor_enrichment_over_poset P₁ P₂ F).
  - abstract
      (intro EF ;
       use subtypePath ; [ intro ; apply isaprop_is_functor_enrichment | ] ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use eq_monotone_function ;
       intro f ;
       cbn ;
       exact (eqtohomot (maponpaths pr1 (functor_enrichment_from_arr EF f)) tt)).
  - abstract
      (intros EF ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use funextsec ; intro f ;
       use funextsec ; intro g ;
       use funextsec ; intro p ;
       apply propproperty).
Defined.
