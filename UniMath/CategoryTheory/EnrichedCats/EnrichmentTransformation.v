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
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
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
  intros x y ; cbn.
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
  intros x y ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite <- !(functor_enrichment_id FE).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply tensor_comp_mor.
  }
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    apply enrichment_id_right.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply mon_rinvunitor_runitor.
  }
  refine (id_left _ @ _).
  refine (!_).
  rewrite (tensor_comp_r_id_l _ _ (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    apply enrichment_id_left.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply mon_linvunitor_lunitor.
  }
  apply id_left.
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
  intros x y ; cbn.
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
  intros x y ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite <- !(functor_enrichment_id FE).
  rewrite (tensor_comp_r_id_l _ _ (FE x y)).
  rewrite !assoc'.
  rewrite <- functor_enrichment_comp.
  rewrite id_right.
  rewrite (tensor_comp_l_id_l (FE x y)).
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
  intros x y ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite !assoc'.
  rewrite <- !(functor_enrichment_id HE).
  rewrite <- !(functor_enrichment_id GE).
  rewrite <- !(functor_enrichment_id FE).
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    rewrite !assoc.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    apply tensor_comp_l_id_l.
  }
  rewrite !assoc'.
  rewrite <- (functor_enrichment_comp HE).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        rewrite <- (functor_enrichment_comp GE).
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- (functor_enrichment_comp FE).
      apply idpath.
    }
    rewrite !assoc.
    do 3 apply maponpaths_2.
    refine (!_).
    apply enrichment_id_right.
  }
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply mon_rinvunitor_runitor.
    }
    apply id_left.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply maponpaths_2.
    rewrite !assoc.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    apply tensor_comp_r_id_l.
  }
  rewrite !assoc'.
  rewrite <- (functor_enrichment_comp HE).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        rewrite <- (functor_enrichment_comp GE).
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- (functor_enrichment_comp FE).
      apply idpath.
    }
    rewrite !assoc.
    do 3 apply maponpaths_2.
    refine (!_).
    apply enrichment_id_left.
  }
  rewrite !assoc.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply mon_linvunitor_lunitor.
  }
  rewrite id_left.
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
  intros x y ; cbn.
  rewrite !enriched_from_arr_id.
  rewrite !assoc'.
  rewrite <- !(functor_enrichment_id HE).
  rewrite <- !(functor_enrichment_id GE).
  rewrite <- !(functor_enrichment_id FE).
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    rewrite !assoc.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    apply tensor_comp_l_id_l.
  }
  rewrite !assoc'.
  rewrite <- (functor_enrichment_comp HE).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        rewrite <- (functor_enrichment_comp GE).
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- (functor_enrichment_comp FE).
      apply idpath.
    }
    rewrite !assoc.
    do 3 apply maponpaths_2.
    refine (!_).
    apply enrichment_id_right.
  }
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply mon_rinvunitor_runitor.
    }
    apply id_left.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply maponpaths_2.
    rewrite !assoc.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    refine (tensor_comp_mor _ _ _ _ @ _).
    apply maponpaths_2.
    apply tensor_comp_r_id_l.
  }
  rewrite !assoc'.
  rewrite <- (functor_enrichment_comp HE).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite assoc.
        rewrite <- (functor_enrichment_comp GE).
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- (functor_enrichment_comp FE).
      apply idpath.
    }
    rewrite !assoc.
    do 3 apply maponpaths_2.
    refine (!_).
    apply enrichment_id_left.
  }
  rewrite !assoc.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply mon_linvunitor_lunitor.
  }
  rewrite id_left.
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
  intros x y ; cbn.
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
  intros x y ; cbn.
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
  pose (H x y).
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
