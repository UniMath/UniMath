(******************************************************************************************

 Invertible transformations of profunctors

 In this file, we define invertible transformations of profunctors. These are transformations
 that are pointwise an isomorphism. We also show that their inverse is again a transformation
 of profunctors and we prove the inverse laws. Finally, we characterize the identity type of
 enriched profunctors via invertible enriched transformations. This proof follows the proof
 of univalence for functor categories.

 Content
 1. Invertible profunctor transformations
 2. The inverse transformation
 3. The identity type of enriched profunctors

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section InvertibleTransformation.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {P Q : E₁ ↛e E₂}
          (τ : enriched_profunctor_transformation P Q).

  (** * 1. Invertible profunctor transformations *)
  Definition is_iso_enriched_profunctor_transformation
    : UU
    := ∏ (y : C₂) (x : C₁), is_z_isomorphism (τ y x).

  Proposition isaprop_is_iso_enriched_profunctor_transformation
    : isaprop is_iso_enriched_profunctor_transformation.
  Proof.
    use impred ; intro y.
    use impred ; intro x.
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition pointwise_iso_enriched_profunctor_transformation
             (Hτ : is_iso_enriched_profunctor_transformation)
             (y : C₂)
             (x : C₁)
    : z_iso (P y x) (Q y x)
    := _ ,, Hτ y x.

  (** * 2. The inverse transformation *)
  Definition pointwise_inv_enriched_profunctor_transformation
             (Hτ : is_iso_enriched_profunctor_transformation)
             (y : C₂)
             (x : C₁)
    : Q y x --> P y x
    := inv_from_z_iso (pointwise_iso_enriched_profunctor_transformation Hτ y x).

  Section Inverse.
    Context (Hτ : is_iso_enriched_profunctor_transformation).

    Proposition inv_enriched_profunctor_transformation_laws
      : enriched_profunctor_transformation_laws
          (pointwise_inv_enriched_profunctor_transformation Hτ).
    Proof.
      split.
      - intros y₁ y₂ x ; cbn.
        unfold pointwise_inv_enriched_profunctor_transformation.
        use z_iso_inv_on_left ; cbn.
        rewrite !assoc'.
        rewrite <- enriched_profunctor_transformation_lmap_e.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite z_iso_after_z_iso_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      - intros y x₁ x₂ ; cbn.
        unfold pointwise_inv_enriched_profunctor_transformation.
        use z_iso_inv_on_left ; cbn.
        rewrite !assoc'.
        rewrite <- enriched_profunctor_transformation_rmap_e.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite z_iso_after_z_iso_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition inv_enriched_profunctor_transformation
      : enriched_profunctor_transformation Q P.
    Proof.
      use make_enriched_profunctor_transformation.
      - exact (pointwise_inv_enriched_profunctor_transformation Hτ).
      - exact inv_enriched_profunctor_transformation_laws.
    Defined.
  End Inverse.

  Proposition inv_enriched_profunctor_transformation_left
              (Hτ : is_iso_enriched_profunctor_transformation)
    : enriched_profunctor_comp_transformation
        (inv_enriched_profunctor_transformation Hτ)
        τ
      =
      enriched_profunctor_id_transformation _.
  Proof.
    use eq_enriched_profunctor_transformation.
    intros y x ; cbn.
    unfold pointwise_inv_enriched_profunctor_transformation.
    apply z_iso_after_z_iso_inv.
  Qed.

  Proposition inv_enriched_profunctor_transformation_right
              (Hτ : is_iso_enriched_profunctor_transformation)
    : enriched_profunctor_comp_transformation
        τ
        (inv_enriched_profunctor_transformation Hτ)
      =
      enriched_profunctor_id_transformation _.
  Proof.
    use eq_enriched_profunctor_transformation.
    intros y x ; cbn.
    unfold pointwise_inv_enriched_profunctor_transformation.
    exact (z_iso_inv_after_z_iso
             (pointwise_iso_enriched_profunctor_transformation Hτ y x)).
  Qed.
End InvertibleTransformation.

Arguments pointwise_inv_enriched_profunctor_transformation {V C₁ C₂ E₁ E₂ P Q τ} Hτ y x /.

(** * 3. The identity type of enriched profunctors *)
Definition enriched_profunctor_data_eq_weq_help
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : pr1 P ╝ pr1 Q
    ≃
    ∑ (p : ∏ (y : C₂) (x : C₁), P y x = Q y x),
    (∏ (y₁ y₂ : C₂) (x : C₁),
     identity _ #⊗ idtoiso (p y₁ x) · lmap_e Q y₁ y₂ x
     =
     lmap_e P y₁ y₂ x · idtoiso (p y₂ x))
    ×
    (∏ (y : C₂) (x₁ x₂ : C₁),
     identity _ #⊗ idtoiso (p y x₁) · rmap_e Q y x₁ x₂
     =
     rmap_e P y x₁ x₂ · idtoiso (p y x₂)).
Proof.
  use weqbandf.
  - refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers ; intro y.
    apply weqtoforallpaths.
  - intro p ; cbn.
    induction P as [ P HP ].
    induction P as [ Po Pm ].
    induction Q as [ Q HQ ].
    induction Q as [ Qo Qm ].
    cbn in *.
    induction p ; cbn.
    refine (_ ∘ pathsdirprodweq)%weq.
    use weqdirprodf.
    + abstract
        (refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro y₁ ;
         refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro y₂ ;
         refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro x ; cbn ;
         rewrite tensor_id_id ;
         rewrite id_left ;
         rewrite id_right ;
         cbn ;
         exact (weqpathsinv0 _ _)).
    + abstract
        (refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro y₁ ;
         refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro y₂ ;
         refine (_ ∘ weqtoforallpaths _ _ _)%weq ;
         use weqonsecfibers ; intro x ; cbn ;
         rewrite tensor_id_id ;
         rewrite id_left ;
         rewrite id_right ;
         cbn ;
         exact (weqpathsinv0 _ _)).
Defined.

Definition enriched_profunctor_data_eq_weq
           {V : sym_mon_closed_cat}
           (HV : is_univalent V)
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : pr1 P ╝ pr1 Q
    ≃
    ∑ (f : ∏ (y : C₂) (x : C₁), z_iso (P y x) (Q y x)),
    (∏ (y₁ y₂ : C₂) (x : C₁),
     identity _ #⊗ f y₁ x · lmap_e Q y₁ y₂ x
     =
     lmap_e P y₁ y₂ x · f y₂ x)
    ×
    (∏ (y : C₂) (x₁ x₂ : C₁),
     identity _ #⊗ f y x₁ · rmap_e Q y x₁ x₂
     =
     rmap_e P y x₁ x₂ · f y x₂).
Proof.
  refine (_ ∘ enriched_profunctor_data_eq_weq_help P Q)%weq.
  use weqbandf.
  - use weqonsecfibers ; intro y.
    use weqonsecfibers ; intro x.
    cbn.
    exact (make_weq _ (HV _ _)).
  - intros τ.
    apply idweq.
Defined.

Definition enriched_profunctor_univalent_cat_help
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : (∑ (f : ∏ (y : C₂) (x : C₁), z_iso (P y x) (Q y x)),
    (∏ (y₁ y₂ : C₂) (x : C₁),
     identity _ #⊗ f y₁ x · lmap_e Q y₁ y₂ x
     =
     lmap_e P y₁ y₂ x · f y₂ x)
    ×
    (∏ (y : C₂) (x₁ x₂ : C₁),
     identity _ #⊗ f y x₁ · rmap_e Q y x₁ x₂
     =
     rmap_e P y x₁ x₂ · f y x₂))
    ≃
    ∑ (τ : enriched_profunctor_transformation P Q),
    is_iso_enriched_profunctor_transformation τ.
Proof.
  use weq_iso.
  - intros τ.
    simple refine (_ ,, _).
    + use make_enriched_profunctor_transformation.
      * exact (λ y x, pr1 τ y x).
      * exact (pr2 τ).
    + intros y x.
      apply z_iso_is_z_isomorphism.
  - intro τ.
    simple refine (_ ,, _ ,, _).
    + refine (λ y x, pr1 τ y x ,, _).
      apply (pr2 τ).
    + intros.
      apply enriched_profunctor_transformation_lmap_e.
    + intros y x₁ x₂.
      apply enriched_profunctor_transformation_rmap_e.
  - abstract
      (intro ;
       apply idpath).
  - abstract
      (intro ;
       apply idpath).
Defined.

Definition enriched_profunctor_univalent_cat
           {V : sym_mon_closed_cat}
           (HV : is_univalent V)
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : P = Q
    ≃
    ∑ (τ : enriched_profunctor_transformation P Q),
    is_iso_enriched_profunctor_transformation τ.
Proof.
  refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
  {
    apply isaprop_enriched_profunctor_laws.
  }
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  refine (_ ∘ enriched_profunctor_data_eq_weq HV P Q)%weq.
  apply enriched_profunctor_univalent_cat_help.
Defined.
