(*****************************************************************

 Enrichments of transformations

 In this file, we define enriched transformations. The definition
 is based on the same ideas as used in the definition for
 enrichments for categories and for functors.

 We also show that every natural transformation can be enriched
 if the monoidal category is faithful.

 Contents
 1. Natural transformations with enrichments
 2. The identity transformation
 3. The unitors
 4. The associators
 5. Composition
 6. Enriched transformations on faithful monoidal categories

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.whiskering.

Opaque mon_lunitor mon_linvunitor.
Opaque mon_runitor mon_rinvunitor.
Opaque mon_lassociator mon_rassociator.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Natural transformations with enrichments
 *)
Definition nat_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : nat_trans_data F G)
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
  := ∑ (τ : nat_trans_data F G), nat_trans_enrichment τ (pr2 F) (pr2 G).

Definition isaprop_nat_trans_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : nat_trans_data F G)
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
  use funextsec.
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
  - use impred_isaset.
    intro.
    apply homset_property.
  - intro.
    apply isasetaprop.
    do 2 (use impred ; intro).
    apply homset_property.
Qed.

Proposition nat_trans_enrichment_via_comp
            {V : monoidal_cat}
            {C₁ C₂ : category}
            {F G : C₁ ⟶ C₂}
            (τ : nat_trans_data F G)
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (p : ∏ (x y : C₁),
                 EG x y · precomp_arr E₂ (G y) (τ x)
                 =
                 EF x y · postcomp_arr E₂ (F x) (τ y))
  : nat_trans_enrichment τ EF EG.
Proof.
  intros x y.
  refine (_ @ p x y @ _) ; unfold postcomp_arr, precomp_arr.
  - rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_rinvunitor.
    rewrite !assoc'.
    rewrite <- tensor_split'.
    apply idpath.
  - rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    rewrite <- tensor_split.
    apply idpath.
Qed.

Proposition nat_trans_enrichment_to_comp
            {V : monoidal_cat}
            {C₁ C₂ : category}
            {F G : C₁ ⟶ C₂}
            {τ : nat_trans_data F G}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (Eτ : nat_trans_enrichment τ EF EG)
            (x y : C₁)
  : EG x y · precomp_arr E₂ (G y) (τ x)
    =
    EF x y · postcomp_arr E₂ (F x) (τ y).
Proof.
  refine (_ @ Eτ x y @ _) ; unfold postcomp_arr, precomp_arr.
  - rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_rinvunitor.
    rewrite !assoc'.
    rewrite <- tensor_split'.
    apply idpath.
  - rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    rewrite <- tensor_split.
    apply idpath.
Qed.

Proposition nat_z_iso_inv_enrichment
            {V : monoidal_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F G : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (τ : nat_z_iso F G)
            (Eτ : nat_trans_enrichment τ EF EG)
  : nat_trans_enrichment (nat_z_iso_inv τ) EG EF.
Proof.
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  refine (!(id_right _) @ _).
  rewrite <- postcomp_arr_id.
  etrans.
  {
    do 2 apply maponpaths.
    exact (!(z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso τ y))).
  }
  rewrite postcomp_arr_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite precomp_postcomp_arr.
  cbn.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply (!nat_trans_enrichment_to_comp Eτ x y).
  }
  rewrite !assoc'.
  rewrite <- precomp_arr_comp.
  etrans.
  {
    do 2 apply maponpaths.
    exact (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
  }
  rewrite precomp_arr_id.
  apply id_right.
Qed.

(**
 2. The identity transformation
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_right.
  apply idpath.
Qed.

(**
 3. The unitors
 *)
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_left, !id_right.
  apply idpath.
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_left, !id_right.
  apply idpath.
Qed.

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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_right.
  apply idpath.
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_right.
  apply idpath.
Qed.

(**
 4. The associators
 *)
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_right.
  rewrite !assoc'.
  apply idpath.
Qed.

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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_id, postcomp_arr_id.
  rewrite !id_right.
  rewrite !assoc'.
  apply idpath.
Qed.

(**
 5. Composition
 *)
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite precomp_arr_comp, postcomp_arr_comp.
  rewrite !assoc.
  rewrite (nat_trans_enrichment_to_comp τE₂).
  rewrite !assoc'.
  rewrite <- precomp_postcomp_arr.
  rewrite !assoc.
  rewrite (nat_trans_enrichment_to_comp τE₁).
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite !assoc'.
  apply maponpaths.
  rewrite (nat_trans_enrichment_to_comp τE).
  apply idpath.
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
  use nat_trans_enrichment_via_comp.
  intros x y ; cbn.
  rewrite !assoc'.
  rewrite (functor_enrichment_precomp_arr GE).
  rewrite (functor_enrichment_postcomp_arr GE).
  rewrite !assoc.
  apply maponpaths_2.
  rewrite (nat_trans_enrichment_to_comp τE).
  apply idpath.
Qed.

(**
 6. Enriched transformations on faithful monoidal categories
 *)
Definition is_nat_trans_from_enrichment
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {τ : nat_trans_data F G}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {FE : functor_enrichment F E₁ E₂}
           {GE : functor_enrichment G E₁ E₂}
           (H : nat_trans_enrichment τ FE GE)
  : is_nat_trans _ _ τ.
Proof.
  intros x y f.
  pose (H x y) as p.
  cbn in p.
  use (invmaponpathsweq (_ ,, isweq_enriched_from_arr E₂ _ _)).
  cbn.
  rewrite !enriched_from_arr_comp.
  rewrite (functor_enrichment_from_arr FE).
  rewrite (functor_enrichment_from_arr GE).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply tensor_comp_l_id_l.
  }
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_linvunitor.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply tensor_comp_r_id_l.
  }
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  exact p.
Qed.

Definition faithful_moncat_nat_trans_enrichment
           {V : monoidal_cat}
           (HV : faithful_moncat V)
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : F ⟹ G)
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (FE : functor_enrichment F E₁ E₂)
           (GE : functor_enrichment G E₁ E₂)
  : nat_trans_enrichment τ FE GE.
Proof.
  intros x y.
  use HV.
  intros a.
  pose (maponpaths
          (λ z, enriched_from_arr E₂ z)
          (nat_trans_ax τ x y (enriched_to_arr E₁ a))) as p.
  cbn in p.
  rewrite !enriched_from_arr_comp in p.
  rewrite (functor_enrichment_from_arr FE) in p.
  rewrite (functor_enrichment_from_arr GE) in p.
  rewrite !enriched_from_to_arr in p.
  refine (_ @ !p @ _).
  - rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply tensor_comp_r_id_l.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    refine (!_).
    apply tensor_rinvunitor.
  - rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply tensor_comp_l_id_l.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    apply tensor_linvunitor.
Qed.
