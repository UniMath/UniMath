(**********************************************************************

 The enriched category of dialgebras

 We construct an enrichment over the category of dialgebras between
 two enriched functors. In addition, we show that this gives rise to
 inserters in the bicategory of enriched categories.

 Note that to construct this enrichment, we assume that the monoidal
 category `V` has equalizers. This is because morphisms in the
 category of dialgebras come with a requirement that a certain diagram
 commutes. As such, this requirement must also be present in the
 enrichment. To formulate this requirement, we use equalizers.

 Contents
 1. The enrichment of dialgebras
 2. Enrichment of the first projection
 3. Enrichment of functors to dialgebras
 4. Enrichment of natural transformations to dialgebras

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor.

Section EnrichedDialgebras.
  Context (V : monoidal_cat)
          (EV : Equalizers V)
          {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (FE : functor_enrichment F E₁ E₂)
          (GE : functor_enrichment G E₁ E₂).

  (**
   1. The enrichment of dialgebras
   *)
  Definition dialgebra_enrichment_mor_left
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
    : E₁ ⦃ x , y ⦄ --> E₂ ⦃ F x , G y ⦄
    := GE x y
       · mon_rinvunitor _
       · identity _ #⊗ enriched_from_arr E₂ f
       · enriched_comp _ _ _ _.

  Definition dialgebra_enrichment_mor_right
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
    : E₁ ⦃ x , y ⦄ --> E₂ ⦃ F x , G y ⦄
    := FE x y
       · mon_linvunitor _
       · enriched_from_arr E₂ g #⊗ identity _
       · enriched_comp _ _ _ _.

  Definition dialgebra_enrichment_mor
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
    : V
    := EV _ _
         (dialgebra_enrichment_mor_left f g)
         (dialgebra_enrichment_mor_right f g).

  Definition dialgebra_enrichment_mor_incl
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
    : dialgebra_enrichment_mor f g --> E₁ ⦃ x , y ⦄
    := EqualizerArrow
         (EV _ _
             (dialgebra_enrichment_mor_left f g)
             (dialgebra_enrichment_mor_right f g)).

  Definition dialgebra_enrichment_mor_incl_eq
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
    : dialgebra_enrichment_mor_incl f g · dialgebra_enrichment_mor_left f g
      =
      dialgebra_enrichment_mor_incl f g · dialgebra_enrichment_mor_right f g.
  Proof.
    exact (EqualizerEqAr
             (EV _ _
                (dialgebra_enrichment_mor_left f g)
                (dialgebra_enrichment_mor_right f g))).
  Qed.


  Definition dialgebra_enrichment_mor_eq_of_mor
             {x y : C₁}
             (f : F x --> G x)
             (g : F y --> G y)
             {v : V}
             {φ₁ φ₂ : v --> dialgebra_enrichment_mor f g}
             (p : φ₁ · dialgebra_enrichment_mor_incl f g
                  =
                  φ₂ · dialgebra_enrichment_mor_incl f g)
    : φ₁ = φ₂.
  Proof.
    use (isEqualizerInsEq
           (pr22 (EV _ _
                     (dialgebra_enrichment_mor_left f g)
                     (dialgebra_enrichment_mor_right f g)))).
    exact p.
  Qed.

  Definition dialgebra_enrichment_id_eq
             {x : C₁}
             (f : F x --> G x)
    : enriched_id E₁ x · dialgebra_enrichment_mor_left f f
      =
      enriched_id E₁ x · dialgebra_enrichment_mor_right f f.
  Proof.
    unfold dialgebra_enrichment_mor_left, dialgebra_enrichment_mor_right.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply tensor_rinvunitor.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite id_left, id_right.
    rewrite !assoc.
    rewrite tensor_rinvunitor.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_linvunitor.
      apply idpath.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite id_left, id_right.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    rewrite !id_left.
    rewrite (functor_enrichment_id FE).
    rewrite (functor_enrichment_id GE).
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite <- enrichment_id_right.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite <- enrichment_id_left.
    rewrite tensor_lunitor.
    rewrite tensor_runitor.
    apply maponpaths_2.
    apply mon_lunitor_I_mon_runitor_I.
  Qed.

  Definition dialgebra_enrichment_id
             {x : C₁}
             (f : F x --> G x)
    : 𝟙 --> dialgebra_enrichment_mor f f.
  Proof.
    use EqualizerIn.
    - exact (enriched_id E₁ x).
    - exact (dialgebra_enrichment_id_eq f).
  Defined.

  Definition dialgebra_enrichment_id_incl
             {x : C₁}
             (f : F x --> G x)
    : dialgebra_enrichment_id f · dialgebra_enrichment_mor_incl f f
      =
      enriched_id E₁ x.
  Proof.
    apply EqualizerCommutes.
  Qed.

  Definition dialgebra_enrichment_comp_mor
             {x y z : C₁}
             (f₁ : F x --> G x)
             (f₂ : F y --> G y)
             (f₃ : F z --> G z)
    : dialgebra_enrichment_mor f₂ f₃ ⊗ dialgebra_enrichment_mor f₁ f₂
      -->
      E₁ ⦃ x, z ⦄
    := dialgebra_enrichment_mor_incl f₂ f₃ #⊗ dialgebra_enrichment_mor_incl f₁ f₂
       · enriched_comp _ _ _ _.

  Definition dialgebra_enrichment_comp_eq
             {x y z : C₁}
             (f₁ : F x --> G x)
             (f₂ : F y --> G y)
             (f₃ : F z --> G z)
    : dialgebra_enrichment_comp_mor f₁ f₂ f₃
      · dialgebra_enrichment_mor_left f₁ f₃
      =
      dialgebra_enrichment_comp_mor f₁ f₂ f₃
      · dialgebra_enrichment_mor_right f₁ f₃.
  Proof.
    unfold dialgebra_enrichment_comp_mor.
    unfold dialgebra_enrichment_mor_left, dialgebra_enrichment_mor_right.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    rewrite (functor_enrichment_comp FE).
    rewrite (functor_enrichment_comp GE).
    rewrite !assoc.
    rewrite <- !tensor_comp_mor.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply tensor_rinvunitor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply tensor_linvunitor.
    }
    refine (!_).
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)).
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      refine (!(tensor_split' _ _) @ _).
      apply tensor_split.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply tensor_split'.
    }
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply enrichment_assoc.
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply enrichment_assoc'.
    }
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)).
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (!_).
        apply tensor_id_id.
      }
      apply tensor_rassociator.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_id_id.
      }
      apply tensor_lassociator.
    }
    rewrite <- mon_rinvunitor_triangle.
    rewrite <- mon_linvunitor_triangle.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)).
    etrans.
    {
      do 2 apply maponpaths.
      do 3 apply maponpaths_2.
      apply mon_rassociator_lassociator.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      do 3 apply maponpaths_2.
      apply mon_lassociator_rassociator.
    }
    rewrite !assoc.
    rewrite <- !tensor_comp_mor.
    rewrite !id_right.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite !id_right.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (_ @ dialgebra_enrichment_mor_incl_eq f₁ f₂).
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply idpath.
    }
    unfold dialgebra_enrichment_mor_right.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (_ @ !(dialgebra_enrichment_mor_incl_eq f₂ f₃)).
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply idpath.
    }
    unfold dialgebra_enrichment_mor_left.
    rewrite !tensor_comp_mor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite tensor_comp_r_id_r.
    rewrite tensor_comp_l_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply enrichment_assoc.
    }
    rewrite !assoc.
    rewrite tensor_comp_l_id_r.
    do 2 apply maponpaths_2.
    rewrite tensor_comp_r_id_r.
    rewrite tensor_comp_l_id_r.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply tensor_lassociator.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    apply mon_inv_triangle.
  Qed.

  Definition dialgebra_enrichment_comp
             {x y z : C₁}
             (f₁ : F x --> G x)
             (f₂ : F y --> G y)
             (f₃ : F z --> G z)
    : dialgebra_enrichment_mor f₂ f₃ ⊗ dialgebra_enrichment_mor f₁ f₂
      -->
      dialgebra_enrichment_mor f₁ f₃.
  Proof.
    use EqualizerIn.
    - exact (dialgebra_enrichment_comp_mor f₁ f₂ f₃).
    - exact (dialgebra_enrichment_comp_eq f₁ f₂ f₃).
  Defined.

  Definition dialgebra_enrichment_comp_incl
             {x y z : C₁}
             (f₁ : F x --> G x)
             (f₂ : F y --> G y)
             (f₃ : F z --> G z)
    : dialgebra_enrichment_comp f₁ f₂ f₃ · dialgebra_enrichment_mor_incl f₁ f₃
      =
      dialgebra_enrichment_comp_mor f₁ f₂ f₃.
  Proof.
    apply EqualizerCommutes.
  Qed.

  Definition dialgebra_enrichment_from_arr_eq
             {x y : C₁}
             {f : F x --> G x}
             {g : F y --> G y}
             (h : x --> y)
             (p : f · # G h = # F h · g)
    : enriched_from_arr E₁ h · dialgebra_enrichment_mor_left f g
      =
      enriched_from_arr E₁ h · dialgebra_enrichment_mor_right f g.
  Proof.
    unfold dialgebra_enrichment_mor_left, dialgebra_enrichment_mor_right.
    rewrite !assoc.
    rewrite tensor_rinvunitor.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite !id_left, !id_right.
    rewrite <- (functor_enrichment_from_arr FE).
    rewrite <- (functor_enrichment_from_arr GE).
    use (invmaponpathsweq (_ ,, isweq_enriched_to_arr E₂ _ _)).
    cbn.
    rewrite mon_rinvunitor_I_mon_linvunitor_I.
    rewrite !assoc.
    rewrite <- !(enriched_to_arr_comp E₂).
    exact (!p).
  Qed.

  Definition dialgebra_enrichment_from_arr
             {x y : C₁}
             {f : F x --> G x}
             {g : F y --> G y}
             (h : x --> y)
             (p : f · # G h = # F h · g)
    : 𝟙 --> dialgebra_enrichment_mor f g.
  Proof.
    use EqualizerIn.
    - exact (enriched_from_arr E₁ h).
    - exact (dialgebra_enrichment_from_arr_eq h p).
  Defined.

  Definition dialgebra_enrichment_from_arr_incl
             {x y : C₁}
             {f : F x --> G x}
             {g : F y --> G y}
             (h : x --> y)
             (p : f · # G h = # F h · g)
    : dialgebra_enrichment_from_arr h p · dialgebra_enrichment_mor_incl f g
      =
      enriched_from_arr E₁ h.
  Proof.
    apply EqualizerCommutes.
  Defined.

  Definition dialgebra_enrichment_to_arr_mor
             {x y : C₁}
             {f : F x --> G x}
             {g : F y --> G y}
             (h : 𝟙 --> dialgebra_enrichment_mor f g)
    :  x --> y
    := enriched_to_arr E₁ (h · dialgebra_enrichment_mor_incl _ _).

  Definition dialgebra_enrichment_to_arr_eq
             {x y : C₁}
             {f : F x --> G x}
             {g : F y --> G y}
             (h : 𝟙 --> dialgebra_enrichment_mor f g)
    : f · # G (dialgebra_enrichment_to_arr_mor h)
      =
      # F (dialgebra_enrichment_to_arr_mor h) · g.
  Proof.
    unfold dialgebra_enrichment_to_arr_mor.
    use (invmaponpathsweq (_ ,, isweq_enriched_from_arr E₂ _ _)).
    cbn.
    rewrite !enriched_from_arr_comp.
    rewrite (functor_enrichment_from_arr FE).
    rewrite (functor_enrichment_from_arr GE).
    rewrite !enriched_from_to_arr.
    pose (dialgebra_enrichment_mor_incl_eq f g) as p.
    unfold dialgebra_enrichment_mor_left in p.
    unfold dialgebra_enrichment_mor_right in p.
    rewrite !assoc in p.
    rewrite tensor_rinvunitor in p.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply tensor_comp_r_id_l.
    }
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
      refine (_ @ p).
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_right, id_left.
      apply idpath.
    }
    clear p.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_linvunitor.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Definition dialgebra_enrichment_data
    : enrichment_data (dialgebra F G) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ f g, dialgebra_enrichment_mor (pr2 f) (pr2 g)).
    - exact (λ f, dialgebra_enrichment_id (pr2 f)).
    - exact (λ f₁ f₂ f₃, dialgebra_enrichment_comp (pr2 f₁) (pr2 f₂) (pr2 f₃)).
    - exact (λ f g τ, dialgebra_enrichment_from_arr (pr1 τ) (pr2 τ)).
    - refine (λ f g τ, dialgebra_enrichment_to_arr_mor τ ,, _).
      exact (dialgebra_enrichment_to_arr_eq τ).
  Defined.

  Definition dialgebra_enrichment_laws
    : enrichment_laws dialgebra_enrichment_data.
  Proof.
    repeat split.
    - intros f g.
      use dialgebra_enrichment_mor_eq_of_mor.
      cbn.
      rewrite !assoc'.
      rewrite dialgebra_enrichment_comp_incl.
      unfold dialgebra_enrichment_comp_mor.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_left.
      rewrite dialgebra_enrichment_id_incl.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      apply idpath.
    - intros f g.
      use dialgebra_enrichment_mor_eq_of_mor.
      cbn.
      rewrite !assoc'.
      rewrite dialgebra_enrichment_comp_incl.
      unfold dialgebra_enrichment_comp_mor.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_left.
      rewrite dialgebra_enrichment_id_incl.
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      rewrite tensor_runitor.
      apply idpath.
    - intros w x y z.
      use dialgebra_enrichment_mor_eq_of_mor.
      cbn.
      rewrite !assoc'.
      rewrite !dialgebra_enrichment_comp_incl.
      unfold dialgebra_enrichment_comp_mor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_left.
      rewrite !dialgebra_enrichment_comp_incl.
      unfold dialgebra_enrichment_comp_mor.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_r_id_r.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply enrichment_assoc.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_lassociator.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!(tensor_comp_mor _ _ _ _) @ _ @ tensor_comp_mor _ _ _ _).
      rewrite id_left, id_right.
      apply maponpaths.
      rewrite dialgebra_enrichment_comp_incl.
      apply idpath.
    - intros x y f.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      cbn.
      unfold dialgebra_enrichment_to_arr_mor.
      rewrite dialgebra_enrichment_from_arr_incl.
      apply enriched_to_from_arr.
    - intros x y f.
      cbn.
      use dialgebra_enrichment_mor_eq_of_mor.
      rewrite dialgebra_enrichment_from_arr_incl.
      unfold dialgebra_enrichment_to_arr_mor.
      rewrite enriched_from_to_arr.
      apply idpath.
    - intros f.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      cbn.
      unfold dialgebra_enrichment_to_arr_mor.
      rewrite dialgebra_enrichment_id_incl.
      rewrite enriched_to_arr_id.
      apply idpath.
    - intros x y z f g.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      cbn.
      unfold dialgebra_enrichment_to_arr_mor.
      rewrite !assoc'.
      rewrite dialgebra_enrichment_comp_incl.
      etrans.
      {
        apply (enriched_to_arr_comp E₁ (pr1 f) (pr1 g)).
      }
      apply maponpaths.
      rewrite !assoc'.
      apply maponpaths.
      unfold dialgebra_enrichment_comp_mor.
      rewrite !assoc.
      apply maponpaths_2.
      refine (_ @ tensor_comp_mor _ _ _ _).
      rewrite !dialgebra_enrichment_from_arr_incl.
      apply idpath.
  Qed.

  Definition dialgebra_enrichment
    : enrichment (dialgebra F G) V.
  Proof.
    simple refine (_ ,, _).
    - exact dialgebra_enrichment_data.
    - exact dialgebra_enrichment_laws.
  Defined.

  (**
   2. Enrichment of the first projection
   *)
  Definition dialgebra_pr1_enrichment
    : functor_enrichment (dialgebra_pr1 F G) dialgebra_enrichment E₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ f g, dialgebra_enrichment_mor_incl (pr2 f) (pr2 g)).
    - repeat split.
      + abstract
          (intro f ; cbn ;
           apply dialgebra_enrichment_id_incl).
      + abstract
          (intros x y z ; cbn ;
           apply dialgebra_enrichment_comp_incl).
      + abstract
          (intros x y f ; cbn ;
           refine (!_) ;
           apply dialgebra_enrichment_from_arr_incl).
  Defined.

  Definition dialgebra_nat_trans_enrichment
    : nat_trans_enrichment
        (dialgebra_nat_trans F G)
        (functor_comp_enrichment dialgebra_pr1_enrichment FE)
        (functor_comp_enrichment dialgebra_pr1_enrichment GE).
  Proof.
    intros f g ; cbn.
    unfold dialgebra_nat_trans_data.
    rewrite tensor_comp_r_id_l.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply tensor_rinvunitor.
    }
    pose (dialgebra_enrichment_mor_incl_eq (pr2 f) (pr2 g)) as p.
    refine (_ @ p @ _).
    - unfold dialgebra_enrichment_mor_left.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      apply maponpaths.
      refine (_ @ tensor_comp_mor _ _ _ _).
      rewrite id_left, id_right.
      apply idpath.
    - unfold dialgebra_enrichment_mor_right.
      refine (!_).
      rewrite tensor_comp_l_id_l.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      refine (_ @ tensor_comp_mor _ _ _ _).
      rewrite id_left, id_right.
      apply idpath.
  Qed.

  (**
   3. Enrichment of functors to dialgebras
   *)
  Section FunctorToDialgebraEnrichment.
    Context {C₀ : category}
            {E₀ : enrichment C₀ V}
            {K : C₀ ⟶ C₁}
            {EK : functor_enrichment K E₀ E₁}
            (τ : K ∙ F ⟹ K ∙ G)
            (Eτ : nat_trans_enrichment
                    τ
                    (functor_comp_enrichment EK FE)
                    (functor_comp_enrichment EK GE)).

    Definition nat_trans_to_dialgebra_enrichment_mor_eq
               (x y : C₀)
      : EK x y · dialgebra_enrichment_mor_left (τ x) (τ y)
        =
        EK x y · dialgebra_enrichment_mor_right (τ x) (τ y).
    Proof.
      unfold dialgebra_enrichment_mor_left.
      unfold dialgebra_enrichment_mor_right.
      rewrite !assoc.
      rewrite tensor_rinvunitor.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      refine (!_).
      rewrite !id_left, !id_right.
      rewrite !assoc.
      exact (Eτ x y).
    Qed.

    Definition nat_trans_to_dialgebra_enrichment_mor
               (x y : C₀)
      : E₀ ⦃ x , y ⦄ --> dialgebra_enrichment_mor (τ x) (τ y).
    Proof.
      use EqualizerIn.
      - exact (EK x y).
      - exact (nat_trans_to_dialgebra_enrichment_mor_eq x y).
    Defined.

    Definition nat_trans_to_dialgebra_enrichment_mor_incl
               (x y : C₀)
      : nat_trans_to_dialgebra_enrichment_mor x y
        · dialgebra_enrichment_mor_incl (τ x) (τ y)
        =
        EK x y.
    Proof.
      apply EqualizerCommutes.
    Qed.

    Definition nat_trans_to_dialgebra_enrichment
      : functor_enrichment
          (nat_trans_to_dialgebra K τ)
          E₀
          dialgebra_enrichment.
    Proof.
      simple refine (_ ,, _).
      - exact nat_trans_to_dialgebra_enrichment_mor.
      - repeat split.
        + abstract
            (intros x ;
             use dialgebra_enrichment_mor_eq_of_mor ; cbn ;
             rewrite !assoc' ;
             rewrite nat_trans_to_dialgebra_enrichment_mor_incl ;
             rewrite dialgebra_enrichment_id_incl ;
             apply (functor_enrichment_id EK)).
        + abstract
            (intros x y z ;
             use dialgebra_enrichment_mor_eq_of_mor ; cbn ;
             rewrite !assoc' ;
             rewrite nat_trans_to_dialgebra_enrichment_mor_incl ;
             rewrite dialgebra_enrichment_comp_incl ;
             refine (functor_enrichment_comp EK x y z @ _) ;
             unfold dialgebra_enrichment_comp_mor ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             refine (_ @ tensor_comp_mor _ _ _ _) ;
             rewrite !nat_trans_to_dialgebra_enrichment_mor_incl ;
             apply idpath).
        + abstract
            (intros x y f ;
             use dialgebra_enrichment_mor_eq_of_mor ; cbn ;
             rewrite !assoc' ;
             rewrite nat_trans_to_dialgebra_enrichment_mor_incl ;
             rewrite dialgebra_enrichment_from_arr_incl ;
             apply (functor_enrichment_from_arr EK)).
    Defined.

    Definition nat_trans_to_dialgebra_pr1_enrichment
      : nat_trans_enrichment
          (nat_trans_to_dialgebra_pr1 K τ)
          (functor_comp_enrichment
             nat_trans_to_dialgebra_enrichment
             dialgebra_pr1_enrichment)
          EK.
    Proof.
      intros x y ; cbn.
      rewrite nat_trans_to_dialgebra_enrichment_mor_incl.
      rewrite !enriched_from_arr_id.
      etrans.
      {
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
      }
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_lunitor.
      }
      apply id_left.
    Qed.

    Definition nat_trans_to_dialgebra_pr1_enrichment_inv
      : nat_trans_enrichment
          (nat_z_iso_inv
             (nat_trans_to_dialgebra_pr1_nat_z_iso K τ))
          EK
          (functor_comp_enrichment
             nat_trans_to_dialgebra_enrichment
             dialgebra_pr1_enrichment).
    Proof.
      intros x y ; cbn.
      rewrite nat_trans_to_dialgebra_enrichment_mor_incl.
      rewrite !enriched_from_arr_id.
      etrans.
      {
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
      }
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_lunitor.
      }
      apply id_left.
    Qed.
  End FunctorToDialgebraEnrichment.

  (**
   4. Enrichment of natural transformations to dialgebras
   *)
  Definition build_nat_trans_to_dialgebra_enrichment
             {C₀ : category}
             {E₀ : enrichment C₀ V}
             {H₁ H₂ : C₀ ⟶ dialgebra F G}
             {EH₁ : functor_enrichment H₁ E₀ dialgebra_enrichment}
             {EH₂ : functor_enrichment H₂ E₀ dialgebra_enrichment}
             {τ : H₁ ∙ dialgebra_pr1 F G ⟹ H₂ ∙ dialgebra_pr1 F G}
             (Eτ : nat_trans_enrichment
                     τ
                     (functor_comp_enrichment EH₁ dialgebra_pr1_enrichment)
                     (functor_comp_enrichment EH₂ dialgebra_pr1_enrichment))
             (p : ∏ (x : C₀), pr2 (H₁ x) · # G (τ x) = # F (τ x) · pr2 (H₂ x))
    : nat_trans_enrichment
        (build_nat_trans_to_dialgebra _ _ τ p)
        EH₁
        EH₂.
  Proof.
    intros x y ; cbn.
    use dialgebra_enrichment_mor_eq_of_mor.
    rewrite !assoc'.
    rewrite !dialgebra_enrichment_comp_incl.
    unfold dialgebra_enrichment_comp_mor.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    rewrite !dialgebra_enrichment_from_arr_incl.
    rewrite !assoc.
    exact (Eτ x y).
  Qed.
End EnrichedDialgebras.
