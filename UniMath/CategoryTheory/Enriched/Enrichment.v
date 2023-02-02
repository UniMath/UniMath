(*****************************************************************

 Enrichments of categories

 In this file, we define enrichments of categories, functors, and
 natural transformations. Note that we define these enrichments as
 categories/functors/transformations with extra data and
 properties, whereas the standard definition of enriched category
 does not do so.

 Contents
 1. Enrichments of categories
 2. Functors with enrichments
 3. Examples of functors with enrichments
 4. Natural transformations with enrichments
 5. Examples of natural transformations with enrichments

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.whiskering.

Opaque mon_lunitor mon_linvunitor.
Opaque mon_runitor mon_rinvunitor.
Opaque mon_lassociator mon_rassociator.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Enrichments of categories
 *)
Definition enrichment_data
           (C : precategory_data)
           (V : monoidal_cat)
  : UU
  := ∑ (arr : C → C → V)
       (eI : ∏ (x : C), 𝟙 --> arr x x)
       (eC : ∏ (x y z : C), arr y z ⊗ arr x y --> arr x z),
     (∏ (x y : C), x --> y → 𝟙 --> arr x y)
     ×
     (∏ (x y : C), 𝟙 --> arr x y → x --> y).

Definition arr_enrichment_data
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x y : C)
  : V
  := pr1 E x y.

Notation "E ⦃ x , y ⦄" := (arr_enrichment_data E x y) (at level 49).

Definition enriched_id
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x : C)
  : 𝟙 --> E ⦃ x , x ⦄
  := pr12 E x.

Definition enriched_comp
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x y z : C)
  : (E ⦃ y , z ⦄) ⊗ (E ⦃ x ,  y ⦄) --> E ⦃ x , z ⦄
  := pr122 E x y z.

Definition enriched_from_arr
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           {x y : C}
           (f : x --> y)
  : 𝟙 --> E ⦃ x , y ⦄
  := pr1 (pr222 E) x y f.

Definition enriched_to_arr
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           {x y : C}
           (f : 𝟙 --> E ⦃ x , y ⦄)
  : x --> y
  := pr2 (pr222 E) x y f.

Definition enrichment_laws
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
  : UU
  := (∏ (x y : C),
      mon_lunitor (E ⦃ x , y ⦄)
      =
      enriched_id E y #⊗ identity _ · enriched_comp E x y y)
     ×
     (∏ (x y : C),
      mon_runitor (E ⦃ x , y ⦄)
      =
      identity _ #⊗ enriched_id E x · enriched_comp E x x y)
     ×
     (∏ (w x y z : C),
      enriched_comp E x y z #⊗ identity (E ⦃ w, x ⦄)
      · enriched_comp E w x z
      =
      mon_lassociator _ _ _
      · identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z)
     ×
     (∏ (x y : C) (f : x --> y),
      enriched_to_arr E (enriched_from_arr E f)
      =
      f)
     ×
     (∏ (x y : C) (f : 𝟙 --> E ⦃ x , y ⦄),
      enriched_from_arr E (enriched_to_arr E f)
      =
      f)
     ×
     (∏ (x : C),
      enriched_to_arr E (enriched_id E x)
      =
      identity x)
     ×
     (∏ (x y z : C) (f : x --> y) (g : y --> z),
      f · g
      =
      enriched_to_arr
        E
        (mon_linvunitor 𝟙
         · (enriched_from_arr E g #⊗ enriched_from_arr E f)
         · enriched_comp E x y z)).

Definition isaprop_enrichment_laws
           {C : category}
           {V : monoidal_cat}
           (E : enrichment_data C V)
  : isaprop (enrichment_laws E).
Proof.
  repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enrichment
           (C : category)
           (V : monoidal_cat)
  : UU
  := ∑ (E : enrichment_data C V), enrichment_laws E.

Coercion enrichment_to_data
         {C : category}
         {V : monoidal_cat}
         (E : enrichment C V)
  : enrichment_data C V
  := pr1 E.

Section EnrichmentLaws.
  Context {C : category}
          {V : monoidal_cat}
          (E : enrichment C V).

  Definition enrichment_id_left
             (x y : C)
    : mon_lunitor (E ⦃ x , y ⦄)
      =
      enriched_id E y #⊗ identity _ · enriched_comp E x y y.
  Proof.
    exact (pr12 E x y).
  Qed.

  Definition enrichment_id_right
             (x y : C)
    : mon_runitor (E ⦃ x , y ⦄)
      =
      identity _ #⊗ enriched_id E x · enriched_comp E x x y.
  Proof.
    exact (pr122 E x y).
  Qed.

  Definition enrichment_assoc
             (w x y z : C)
    : enriched_comp E x y z #⊗ identity _
      · enriched_comp E w x z
      =
      mon_lassociator _ _ _
      · identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z.
  Proof.
    exact (pr1 (pr222 E) w x y z).
  Qed.

  Definition enrichment_assoc'
             (w x y z : C)
    : identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z
      =
      mon_rassociator _ _ _
      · enriched_comp E x y z #⊗ identity _
      · enriched_comp E w x z.
  Proof.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply enrichment_assoc.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition enriched_to_from_arr
             {x y : C}
             (f : x --> y)
    : enriched_to_arr E (enriched_from_arr E f)
      =
      f.
  Proof.
    exact (pr12 (pr222 E) x y f).
  Qed.

  Definition enriched_from_to_arr
             {x y : C}
             (f : 𝟙 --> E ⦃ x , y ⦄)
    : enriched_from_arr E (enriched_to_arr E f)
      =
      f.
  Proof.
    exact (pr122 (pr222 E) x y f).
  Qed.

  Definition enriched_to_arr_id
             (x : C)
    : enriched_to_arr E (enriched_id E x)
      =
      identity x.
  Proof.
    exact (pr1 (pr222 (pr222 E)) x).
  Qed.

  Definition enriched_from_arr_id
             (x : C)
    : enriched_from_arr E (identity x)
      =
      enriched_id E x.
  Proof.
    refine (_ @ enriched_from_to_arr _).
    apply maponpaths.
    refine (!_).
    apply enriched_to_arr_id.
  Qed.

  Definition enriched_to_arr_comp
             {x y z : C}
             (f : x --> y)
             (g : y --> z)
    : f · g
      =
      enriched_to_arr
        E
        (mon_linvunitor 𝟙
         · (enriched_from_arr E g #⊗ enriched_from_arr E f)
         · enriched_comp E x y z).
  Proof.
    exact (pr2 (pr222 (pr222 E)) x y z f g).
  Qed.

  Definition enriched_from_arr_comp
             {x y z : C}
             (f : x --> y)
             (g : y --> z)
    : enriched_from_arr
        E
        (f · g)
      =
      mon_linvunitor 𝟙
      · (enriched_from_arr E g #⊗ enriched_from_arr E f)
      · enriched_comp E x y z.
  Proof.
    refine (_ @ enriched_from_to_arr _).
    apply maponpaths.
    apply enriched_to_arr_comp.
  Qed.
End EnrichmentLaws.

Definition cat_with_enrichment
           (V : monoidal_cat)
  : UU
  := ∑ (C : category), enrichment C V.

Coercion cat_with_enrichment_to_cat
         {V : monoidal_cat}
         (E : cat_with_enrichment V)
  : category
  := pr1 E.

Coercion cat_with_enrichment_to_enrichment
         {V : monoidal_cat}
         (E : cat_with_enrichment V)
  : enrichment E V
  := pr2 E.

(**
 2. Functors with enrichments
 *)
Definition functor_enrichment_data
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∏ (x y : C₁), E₁ ⦃ x , y ⦄ --> E₂ ⦃ F x , F y ⦄.

Definition is_functor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment_data F E₁ E₂)
  : UU
  := (∏ (x : C₁),
      enriched_id E₁ x · FE x x
      =
      enriched_id E₂ (F x))
     ×
     (∏ (x y z : C₁),
      enriched_comp E₁ x y z
      · FE x z
      =
      FE y z #⊗ FE x y
      · enriched_comp E₂ (F x) (F y) (F z))
     ×
     (∏ (x y : C₁) (f : x --> y),
      enriched_from_arr E₂ (#F f)
      =
      enriched_from_arr E₁ f · FE x y).

Definition isaprop_is_functor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment_data F E₁ E₂)
  : isaprop (is_functor_enrichment FE).
Proof.
  repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition functor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (FE : functor_enrichment_data F E₁ E₂), is_functor_enrichment FE.

Definition isaset_functor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : isaset (functor_enrichment F E₁ E₂).
Proof.
  use isaset_total2.
  - do 2 (use impred_isaset ; intro).
    apply homset_property.
  - intro.
    apply isasetaprop.
    apply isaprop_is_functor_enrichment.
Qed.

Definition functor_enrichment_to_data
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
           (x y : C₁)
  : E₁ ⦃ x, y ⦄ --> E₂ ⦃ F x, F y ⦄
  := pr1 FE x y.

Coercion functor_enrichment_to_data : functor_enrichment >-> Funclass.

Section FunctorLaws.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (FE : functor_enrichment F E₁ E₂).

  Definition functor_enrichment_id
             (x : C₁)
    : enriched_id E₁ x · FE x x
      =
      enriched_id E₂ (F x).
  Proof.
    exact (pr12 FE x).
  Qed.

  Definition functor_enrichment_comp
             (x y z : C₁)
    : enriched_comp E₁ x y z
      · FE x z
      =
      FE y z #⊗ FE x y
      · enriched_comp E₂ (F x) (F y) (F z).
  Proof.
    exact (pr122 FE x y z).
  Qed.

  Definition functor_enrichment_from_arr
             {x y : C₁}
             (f : x --> y)
    : enriched_from_arr E₂ (#F f)
      =
      enriched_from_arr E₁ f · FE x y.
  Proof.
    exact (pr222 FE x y f).
  Qed.
End FunctorLaws.

Definition functor_with_enrichment
           {V : monoidal_cat}
           (E₁ : cat_with_enrichment V)
           (E₂ : cat_with_enrichment V)
  : UU
  := ∑ (F : E₁ ⟶ E₂), functor_enrichment F E₁ E₂.

Coercion functor_with_enrichment_to_functor
         {V : monoidal_cat}
         {E₁ : cat_with_enrichment V}
         {E₂ : cat_with_enrichment V}
         (F : functor_with_enrichment E₁ E₂)
  : E₁ ⟶ E₂
  := pr1 F.

(**
 3. Examples of functor with enrichments
 *)
Definition functor_id_enrichment_data
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : functor_enrichment_data (functor_identity C) E E
  := λ x y, identity _.

Definition id_is_functor_enrichment
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : is_functor_enrichment (functor_id_enrichment_data E).
Proof.
  repeat split ; unfold functor_id_enrichment_data.
  - intro x ; cbn.
    apply id_right.
  - intros x y z ; cbn.
    rewrite id_right.
    rewrite tensor_id_id.
    rewrite id_left.
    apply idpath.
  - intros x y f ; cbn.
    rewrite id_right.
    apply idpath.
Qed.

Definition functor_id_enrichment
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : functor_enrichment (functor_identity C) E E
  := functor_id_enrichment_data E ,, id_is_functor_enrichment E.

Definition functor_comp_enrichment_data
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ : C₁ ⟶ C₂} {F₂ : C₂ ⟶ C₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (FE₁ : functor_enrichment F₁ E₁ E₂)
           (FE₂ : functor_enrichment F₂ E₂ E₃)
  : functor_enrichment_data (F₁ ∙ F₂) E₁ E₃
  := λ x y, FE₁ x y · FE₂ (F₁ x) (F₁ y).

Definition functor_comp_is_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ : C₁ ⟶ C₂} {F₂ : C₂ ⟶ C₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (FE₁ : functor_enrichment F₁ E₁ E₂)
           (FE₂ : functor_enrichment F₂ E₂ E₃)
  : is_functor_enrichment (functor_comp_enrichment_data FE₁ FE₂).
Proof.
  repeat split ; unfold functor_comp_enrichment_data ; cbn.
  - intros x.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply functor_enrichment_id.
    }
    apply functor_enrichment_id.
  - intros x y z.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply functor_enrichment_comp.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply functor_enrichment_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_comp_mor.
    apply idpath.
  - intros x y f.
    etrans.
    {
      apply (functor_enrichment_from_arr FE₂).
    }
    etrans.
    {
      apply maponpaths_2.
      apply (functor_enrichment_from_arr FE₁).
    }
    rewrite !assoc.
    apply idpath.
Qed.

Definition functor_comp_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ : C₁ ⟶ C₂} {F₂ : C₂ ⟶ C₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (FE₁ : functor_enrichment F₁ E₁ E₂)
           (FE₂ : functor_enrichment F₂ E₂ E₃)
  : functor_enrichment (F₁ ∙ F₂) E₁ E₃
  := functor_comp_enrichment_data FE₁ FE₂ ,, functor_comp_is_enrichment FE₁ FE₂.

(**
 4. Natural transformations with enrichments
 *)
Definition nat_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : F ⟹ G)
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
           (GE : functor_enrichment G E₁ E₂)
  : UU
  := ∏ (x y : C₁),
     mon_rinvunitor (E₁ ⦃ x , y ⦄)
     · GE x y #⊗ enriched_from_arr E₂ (τ x)
     · enriched_comp E₂ _ _ _
     =
     mon_linvunitor (E₁ ⦃ x , y ⦄)
     · enriched_from_arr E₂ (τ y) #⊗ FE x y
     · enriched_comp E₂ _ _ _.

Definition nat_trans_with_enrichment
           {V : monoidal_cat}
           {E₁ : cat_with_enrichment V}
           {E₂ : cat_with_enrichment V}
           (F : functor_with_enrichment E₁ E₂)
           (G : functor_with_enrichment E₁ E₂)
  : UU
  := ∑ (τ : F ⟹ G), nat_trans_enrichment τ (pr2 F) (pr2 G).

Definition isaprop_nat_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : F ⟹ G)
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
           (GE : functor_enrichment G E₁ E₂)
  : isaprop (nat_trans_enrichment τ FE GE).
Proof.
  do 2 (use impred ; intro).
  apply homset_property.
Qed.

Definition eq_nat_trans_with_enrichment
           {V : monoidal_cat}
           {E₁ : cat_with_enrichment V}
           {E₂ : cat_with_enrichment V}
           {F : functor_with_enrichment E₁ E₂}
           {G : functor_with_enrichment E₁ E₂}
           {τ₁ τ₂ : nat_trans_with_enrichment F G}
           (p : ∏ (x : E₁), pr1 τ₁ x = pr1 τ₂ x)
  : τ₁ = τ₂.
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
  exact p.
Qed.

Definition isaset_nat_trans_with_enrichment
           {V : monoidal_cat}
           {E₁ : cat_with_enrichment V}
           {E₂ : cat_with_enrichment V}
           (F : functor_with_enrichment E₁ E₂)
           (G : functor_with_enrichment E₁ E₂)
  : isaset (nat_trans_with_enrichment F G).
Proof.
  use isaset_total2.
  - apply isaset_nat_trans.
    apply homset_property.
  - intro.
    apply isasetaprop.
    do 2 (use impred ; intro).
    apply homset_property.
Qed.

(**
 5. Examples of natural transformations with enrichments
 *)
Definition id_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment (nat_trans_id F) FE FE.
Proof.
  intros x y ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite <- !(functor_enrichment_id FE).
  rewrite (tensor_comp_l_id_l (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite (tensor_comp_r_id_l _ _ (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite <- enrichment_id_left.
  rewrite <- enrichment_id_right.
  etrans.
  {
    apply mon_rinvunitor_runitor.
  }
  refine (!_).
  apply mon_linvunitor_lunitor.
Qed.

Definition lunitor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (nat_trans_id F)
      (functor_comp_enrichment (functor_id_enrichment _) FE)
      FE.
Proof.
  intros x y ; cbn.
  unfold functor_comp_enrichment_data, functor_id_enrichment, functor_id_enrichment_data.
  cbn.
  rewrite !enriched_from_arr_id.
  rewrite <- !(functor_enrichment_id FE).
  rewrite (tensor_comp_l_id_l (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply tensor_comp_mor.
  }
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite <- enrichment_id_left.
  rewrite <- enrichment_id_right.
  refine (!_).
  etrans.
  {
    apply mon_rinvunitor_runitor.
  }
  refine (!_).
  apply mon_linvunitor_lunitor.
Qed.

Definition linvunitor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (nat_trans_id F)
      FE
      (functor_comp_enrichment (functor_id_enrichment _) FE).
Proof.
Admitted.

Definition runitor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (nat_trans_id F)
      (functor_comp_enrichment FE (functor_id_enrichment _))
      FE.
Proof.
  intros x y ; cbn.
  unfold functor_comp_enrichment_data, functor_id_enrichment, functor_id_enrichment_data.
  cbn.
  rewrite !enriched_from_arr_id.
  rewrite <- !(functor_enrichment_id FE).
  rewrite (tensor_comp_l_id_l (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite id_right.
  rewrite (tensor_comp_r_id_l _ _ (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite <- enrichment_id_left.
  rewrite <- enrichment_id_right.
  etrans.
  {
    apply mon_rinvunitor_runitor.
  }
  refine (!_).
  apply mon_linvunitor_lunitor.
Qed.

Definition rinvunitor_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
  : nat_trans_enrichment
      (nat_trans_id F)
      FE
      (functor_comp_enrichment FE (functor_id_enrichment _)).
Proof.
Admitted.

Definition lassociator_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {E₄ : enrichment C₄ V}
           (FE : functor_enrichment F E₁ E₂)
           (GE : functor_enrichment G E₂ E₃)
           (HE : functor_enrichment H E₃ E₄)
  : nat_trans_enrichment
      (nat_trans_id _)
      (functor_comp_enrichment (functor_comp_enrichment FE GE) HE)
      (functor_comp_enrichment FE (functor_comp_enrichment GE HE)).
Proof.
  intros x y ; cbn.
  unfold functor_comp_enrichment, functor_comp_enrichment_data ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite !assoc'.
  rewrite <- !(functor_enrichment_id HE).
  rewrite <- !(functor_enrichment_id GE).
  rewrite <- !(functor_enrichment_id FE).
Admitted.

Definition rassociator_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {E₄ : enrichment C₄ V}
           (FE : functor_enrichment F E₁ E₂)
           (GE : functor_enrichment G E₂ E₃)
           (HE : functor_enrichment H E₃ E₄)
  : nat_trans_enrichment
      (nat_trans_id _)
      (functor_comp_enrichment FE (functor_comp_enrichment GE HE))
      (functor_comp_enrichment (functor_comp_enrichment FE GE) HE).
Proof.
Admitted.

Definition comp_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F₁ F₂ F₃ : C₁ ⟶ C₂}
           {τ₁ : F₁ ⟹ F₂}
           {τ₂ : F₂ ⟹ F₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {FE₁ : functor_enrichment F₁ E₁ E₂}
           {FE₂ : functor_enrichment F₂ E₁ E₂}
           {FE₃ : functor_enrichment F₃ E₁ E₂}
           (τE₁ : nat_trans_enrichment τ₁ FE₁ FE₂)
           (τE₂ : nat_trans_enrichment τ₂ FE₂ FE₃)
  : nat_trans_enrichment (nat_trans_comp _ _ _ τ₁ τ₂) FE₁ FE₃.
Proof.
  intros x y ; cbn.
  pose (p := τE₁ x y).
  pose (q := τE₂ x y).
  rewrite !enriched_from_arr_comp.
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    rewrite tensor_split'.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite tensor_comp_l_id_r.
    apply idpath.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply tensor_comp_l_id_r.
  }
  rewrite !assoc'.
  etrans.
  {
    do 3 apply maponpaths.
    apply enrichment_assoc'.
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply tensor_comp_l_id_r.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply tensor_rassociator.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply mon_rinvunitor_triangle.
  }
  rewrite tensor_id_id.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply tensor_swap'.
    }
    rewrite !assoc.
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc.
  etrans.
  {
    do 3 apply maponpaths_2.
    exact q.
  }
  clear q.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rinvunitor.
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply tensor_swap.
    }
    apply idpath.
  }
  rewrite !assoc'.
  etrans.
  {
    do 3 apply maponpaths.
    apply enrichment_assoc.
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply tensor_id_id.
    }
    apply tensor_lassociator.
  }
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    do 3 apply maponpaths_2.
    rewrite <- mon_rinvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_rassociator_lassociator.
    }
    apply id_right.
  }
  etrans.
  {
    apply maponpaths_2.
    apply tensor_split'.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply tensor_comp_id_l.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_id_l.
    }
    etrans.
    {
      refine (!_).
      apply tensor_comp_id_l.
    }
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply tensor_rinvunitor.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_split'.
    }
    rewrite assoc.
    exact p.
  }
  clear p.
  rewrite !assoc.
  rewrite tensor_comp_l_id_l.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    apply enrichment_assoc'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_comp_l_id_r.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply tensor_rassociator.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply mon_inv_triangle.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_lassociator_rassociator.
    }
    apply id_right.
  }
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    etrans.
    {
      refine (!_).
      apply tensor_comp_id_r.
    }
    apply maponpaths_2.
    apply tensor_rinvunitor.
  }
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply tensor_comp_mor.
  }
  rewrite id_left.
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths_2.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    apply tensor_split'.
  }
  etrans.
  {
    refine (!_).
    apply tensor_comp_mor.
  }
  rewrite id_right.
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  apply idpath.
Qed.

Definition pre_whisker_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G₁ G₂ : C₂ ⟶ C₃}
           {τ : G₁ ⟹ G₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (FE : functor_enrichment F E₁ E₂)
           {GE₁ : functor_enrichment G₁ E₂ E₃}
           {GE₂ : functor_enrichment G₂ E₂ E₃}
           (τE : nat_trans_enrichment τ GE₁ GE₂)
  : nat_trans_enrichment
      (pre_whisker F τ : _ ∙ _ ⟹ _ ∙ _)
      (functor_comp_enrichment FE GE₁)
      (functor_comp_enrichment FE GE₂).
Proof.
  intros x y ; cbn ; unfold functor_comp_enrichment_data.
  pose (p := τE (F x) (F y)).
  rewrite tensor_comp_r_id_l.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    exact p.
  }
  clear p.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_comp_l_id_l.
  rewrite !assoc.
  apply maponpaths_2.
  apply tensor_linvunitor.
Qed.

Definition post_whisker_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ F₂ : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {τ : F₁ ⟹ F₂}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {FE₁ : functor_enrichment F₁ E₁ E₂}
           {FE₂ : functor_enrichment F₂ E₁ E₂}
           (τE : nat_trans_enrichment τ FE₁ FE₂)
           (GE : functor_enrichment G E₂ E₃)
  : nat_trans_enrichment
      (post_whisker τ G : _ ∙ _ ⟹ _ ∙ _)
      (functor_comp_enrichment FE₁ GE)
      (functor_comp_enrichment FE₂ GE).
Proof.
  intros x y ; cbn ; unfold functor_comp_enrichment_data.
  pose (p := τE x y).
  rewrite !(functor_enrichment_from_arr GE).
  rewrite (tensor_comp_mor (FE₂ x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    exact p.
  }
  rewrite !assoc'.
  apply maponpaths.
  rewrite (tensor_comp_mor (enriched_from_arr E₂ (pr1 τ y))).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  apply idpath.
Qed.
