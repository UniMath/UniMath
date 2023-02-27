(*****************************************************************

 Enrichments of functors

 In this file, we define functos with enrichments. The approach
 we take, is the same as for enrichments for categories.

 Contents
 1. Functors with enrichments
 2. Fully faithful functors
 3. The enriched identity functor
 4. The composition of enriched functors

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.limits.terminal.

Opaque mon_lunitor mon_linvunitor.
Opaque mon_runitor mon_rinvunitor.
Opaque mon_lassociator mon_rassociator.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Functors with enrichments
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
 2. Fully faithful functors
 *)
Definition fully_faithful_enriched_functor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {V : monoidal_cat}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : UU
  := ∏ (x y : C₁), is_z_isomorphism (EF x y).

Definition isaprop_fully_faithful_enriched_functor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {V : monoidal_cat}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
  : isaprop (fully_faithful_enriched_functor EF).
Proof.
  repeat (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

Definition fully_faithful_enriched_functor_to_faithful
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {V : monoidal_cat}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (EF : functor_enrichment F E₁ E₂)
           (HEF : fully_faithful_enriched_functor EF)
  : faithful F.
Proof.
  intros x y f.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  refine (!(enriched_to_from_arr E₁ (pr1 φ₁)) @ _).
  refine (_ @ enriched_to_from_arr E₁ (pr1 φ₂)).
  apply maponpaths.
  use (cancel_z_iso _ _ (_ ,, HEF x y)) ; cbn.
  pose (maponpaths (enriched_from_arr E₂) (pr2 φ₁ @ !(pr2 φ₂))) as p.
  rewrite !(functor_enrichment_from_arr EF) in p.
  exact p.
Qed.

(**
 3. The enriched identity functor
 *)
Definition functor_id_enrichment
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : functor_enrichment (functor_identity C) E E.
Proof.
  refine ((λ x y, identity _) ,, _).
  repeat split.
  - abstract
      (intro x ; cbn ;
       apply id_right).
  - abstract
      (intros x y z ; cbn ;
       rewrite id_right ;
       rewrite tensor_id_id ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_right ;
       apply idpath).
Defined.

Definition functor_id_enrichment_fully_faithful
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : fully_faithful_enriched_functor (functor_id_enrichment E).
Proof.
  intros x y.
  apply is_z_isomorphism_identity.
Defined.

(**
 4. The composition of enriched functors
 *)
Definition functor_comp_enrichment
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ : C₁ ⟶ C₂} {F₂ : C₂ ⟶ C₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (FE₁ : functor_enrichment F₁ E₁ E₂)
           (FE₂ : functor_enrichment F₂ E₂ E₃)
  : functor_enrichment (F₁ ∙ F₂) E₁ E₃.
Proof.
  refine ((λ x y, FE₁ x y · FE₂ (F₁ x) (F₁ y)) ,, _).
  repeat split ; cbn.
  - abstract
      (intros x ;
       rewrite !assoc ;
       etrans ;
       [ apply maponpaths_2 ;
         apply functor_enrichment_id
       | ] ;
       apply functor_enrichment_id).
  - abstract
      (intros x y z ;
       rewrite !assoc ;
       etrans ;
       [ apply maponpaths_2 ;
         apply functor_enrichment_comp
       | ] ;
       rewrite !assoc' ;
       etrans ;
       [ apply maponpaths ;
         apply functor_enrichment_comp
       | ] ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       rewrite tensor_comp_mor ;
       apply idpath).
  - abstract
      (intros x y f ;
       etrans ;
       [ apply (functor_enrichment_from_arr FE₂)
       | ] ;
       etrans ;
       [ apply maponpaths_2 ;
         apply (functor_enrichment_from_arr FE₁)
       | ] ;
       rewrite !assoc ;
       apply idpath).
Defined.

Definition functor_comp_enrichment_fully_faithful
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {F₁ : C₁ ⟶ C₂} {F₂ : C₂ ⟶ C₃}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {FE₁ : functor_enrichment F₁ E₁ E₂}
           {FE₂ : functor_enrichment F₂ E₂ E₃}
           (HF₁ : fully_faithful_enriched_functor FE₁)
           (HF₂ : fully_faithful_enriched_functor FE₂)
  : fully_faithful_enriched_functor (functor_comp_enrichment FE₁ FE₂).
Proof.
  intros x y ; cbn.
  use is_z_iso_comp_of_is_z_isos.
  - apply HF₁.
  - apply HF₂.
Defined.

(**

 *)
Definition functor_constant_enrichment
           {V : monoidal_cat}
           (HV : isTerminal V 𝟙)
           {C₁ C₂ : category}
           (a : C₂)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : functor_enrichment (constant_functor _ _ a) E₁ E₂.
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (λ x y, TerminalArrow (_ ,, HV) _ · enriched_id E₂ a).
  - abstract
      (intros x ; cbn ;
       rewrite !assoc ;
       refine (_ @ id_left _) ;
       apply maponpaths_2 ;
       apply (@TerminalArrowEq _ (_ ,, HV))).
  - abstract
      (intros x y z ; cbn ;
       refine (!_) ;
       etrans ;
       [ apply maponpaths_2 ;
         apply tensor_comp_mor
       | ] ;
       rewrite !assoc' ;
       etrans ;
       [ apply maponpaths ;
         rewrite tensor_split ;
         rewrite !assoc' ;
         rewrite <- enrichment_id_left ;
         rewrite tensor_lunitor ;
         apply idpath
       | ] ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply (@TerminalArrowEq _ (_ ,, HV))).
  - abstract
      (intros x y f ; cbn ;
       rewrite enriched_from_arr_id ;
       refine (!(id_left _) @ _) ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply (@TerminalArrowEq _ (_ ,, HV))).
Defined.
