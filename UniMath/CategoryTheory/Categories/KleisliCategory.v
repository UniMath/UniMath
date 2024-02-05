(********************************************************************

 The Kleisli category

 The usual definition of the Kleisli category (given in the file
 `Monads.KleisliCategory.v` does not give rise to a univalent
 category. In this file, we give an alternative definition of the
 Kleisli category in such a way that we do get a univalent category.
 This definition can be found here:

 https://ncatlab.org/nlab/show/Kleisli+category#in_terms_of_free_algebras

 We also prove its universal property.

 Note: to prove its universal property, we use that the usual
 definition of the Kleisli category (which is not necessarily
 univalent), satisfies the universal property. We also use that we
 have a weak equivalence between these two categories.

 Contents
 1. The free algebra functor
 2. The univalent Kleisli category
 3. The weak equivalence
 4. The universal property

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Local Open Scope cat.

(**
 1. The free algebra functor
 *)
Section FreeAlgebraFunctor.
  Context {C : category}
          (m : Monad C).

  Definition free_alg_em_data
    : functor_data C (eilenberg_moore_cat m).
  Proof.
    use make_functor_data.
    - refine (λ x, make_ob_eilenberg_moore m (m x) (μ m x) _ _).
      + apply Monad_law1.
      + refine (!_).
        apply Monad_law3.
    - simple refine (λ x y f, make_mor_eilenberg_moore _ _ _).
      + exact (#m f).
      + exact (!(nat_trans_ax (μ m) _ _ f)).
  Defined.

  Definition free_alg_em_is_functor
    : is_functor free_alg_em_data.
  Proof.
    split.
    - intro x.
      use eq_mor_eilenberg_moore ; cbn.
      apply functor_id.
    - intros x y z f g.
      use eq_mor_eilenberg_moore ; cbn.
      apply functor_comp.
  Qed.

  Definition free_alg_em
    : C ⟶ eilenberg_moore_cat m.
  Proof.
    use make_functor.
    - exact free_alg_em_data.
    - exact free_alg_em_is_functor.
  Defined.
End FreeAlgebraFunctor.

(**
 2. The univalent Kleisli category
 *)
Definition kleisli_cat
           {C : category}
           (m : Monad C)
  : category
  := full_img_sub_precategory (free_alg_em m).

Definition univalent_kleisli_cat
           {C : univalent_category}
           (m : Monad C)
  : univalent_category
  := @univalent_image
       C
       (eilenberg_moore_univalent_cat C m)
       (free_alg_em m).

Definition is_z_iso_kleisli_cat
           {C : category}
           (m : Monad C)
           {x₁ x₂ : kleisli_cat m}
           {f : x₁ --> x₂}
           (Hf : is_z_isomorphism (pr111 f))
  : is_z_isomorphism f.
Proof.
  use is_iso_full_sub.
  use is_z_iso_eilenberg_moore.
  exact Hf.
Defined.

Definition z_iso_kleisli_cat
           {C : category}
           (m : Monad C)
           {x₁ x₂ : kleisli_cat m}
           (f : z_iso (pr1 x₁) (pr1 x₂))
  : z_iso x₁ x₂.
Proof.
  simple refine (_ ,, _).
  - exact (pr1 f ,, tt).
  - use is_iso_full_sub.
    exact (pr2 f).
Defined.

Definition from_z_iso_kleisli_cat
           {C : category}
           (m : Monad C)
           {x₁ x₂ : kleisli_cat m}
           (f : z_iso x₁ x₂)
  : z_iso (pr111 x₁) (pr111 x₂).
Proof.
  use make_z_iso.
  - exact (pr1 (pr111 f)).
  - exact (pr111 (inv_from_z_iso f)).
  - split.
    + exact (maponpaths (λ z, pr111 z) (z_iso_inv_after_z_iso f)).
    + exact (maponpaths (λ z, pr111 z) (z_iso_after_z_iso_inv f)).
Defined.

Definition eq_mor_kleisli_cat
           {C : category}
           (m : Monad C)
           {x₁ x₂ : kleisli_cat m}
           {f₁ f₂ : x₁ --> x₂}
           (p : pr111 f₁ = pr111 f₂)
  : f₁ = f₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  use eq_mor_eilenberg_moore.
  exact p.
Qed.

Definition kleisli_incl
           {C : category}
           (m : Monad C)
  : C ⟶ kleisli_cat m
  := functor_full_img _.

Definition kleisli_nat_trans
           {C : category}
           (m : Monad C)
  : m ∙ kleisli_incl m ⟹ kleisli_incl m.
Proof.
  use make_nat_trans.
  - intro x.
    simple refine (_ ,, tt).
    use make_mor_eilenberg_moore ; cbn.
    + exact (μ m x).
    + abstract
        (refine (!_) ;
         apply Monad_law3).
  - abstract
      (intros x y f ;
       use eq_mor_kleisli_cat ; cbn ;
       apply (nat_trans_ax (μ m))).
Defined.

(**
 3. The weak equivalence
 *)
Definition functor_to_kleisli_cat_data
           {C : category}
           (m : Monad C)
  : functor_data (Kleisli_cat_monad m) (kleisli_cat m).
Proof.
  use make_functor_data.
  - refine (λ x, free_alg_em m x ,, hinhpr (x ,, _)).
    apply identity_z_iso.
  - refine (λ x y f, _ ,, tt).
    use make_mor_eilenberg_moore.
    + exact (# m f · μ m y).
    + abstract
        (cbn ;
         rewrite !assoc ;
         refine (maponpaths (λ z, z · _) (!(nat_trans_ax (μ m) _ _ f)) @ _) ;
         cbn ;
         rewrite !functor_comp ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply Monad_law3).
Defined.

Definition functor_to_kleisli_cat_is_functor
           {C : category}
           (m : Monad C)
  : is_functor (functor_to_kleisli_cat_data m).
Proof.
  split.
  - intro x.
    use eq_mor_kleisli_cat.
    cbn.
    apply Monad_law2.
  - intros x y z f g.
    use eq_mor_kleisli_cat.
    cbn ; unfold bind.
    rewrite !functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax (μ m)).
    }
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    apply Monad_law3.
Qed.

Definition functor_to_kleisli_cat
           {C : category}
           (m : Monad C)
  : Kleisli_cat_monad m ⟶ kleisli_cat m.
Proof.
  use make_functor.
  - exact (functor_to_kleisli_cat_data m).
  - exact (functor_to_kleisli_cat_is_functor m).
Defined.

Definition functor_to_kleisli_cat_incl_nat_trans
           {C : category}
           (m : Monad C)
  : kleisli_incl m
    ⟹
    Left_Kleisli_functor m ∙ functor_to_kleisli_cat m.
Proof.
  use make_nat_trans.
  - refine (λ x, make_mor_eilenberg_moore _ (identity _) _ ,, tt).
    abstract
      (cbn ;
       rewrite functor_id, id_left, id_right ;
       apply idpath).
  - abstract
      (intros x y f ;
       use eq_mor_kleisli_cat ; cbn ;
       rewrite id_left, id_right ;
       rewrite functor_comp ;
       rewrite !assoc' ;
       refine (!_) ;
       refine (_ @ id_right _) ;
       apply maponpaths ;
       apply Monad_law2).
Defined.

Definition functor_to_kleisli_cat_incl_nat_z_iso
           {C : category}
           (m : Monad C)
  : nat_z_iso
      (kleisli_incl m)
      (Left_Kleisli_functor m ∙ functor_to_kleisli_cat m).
Proof.
  use make_nat_z_iso.
  - exact (functor_to_kleisli_cat_incl_nat_trans m).
  - intro.
    use is_z_iso_kleisli_cat.
    apply is_z_isomorphism_identity.
Defined.

Definition full_functor_to_kleisli_cat
           {C : category}
           (m : Monad C)
  : full (functor_to_kleisli_cat m).
Proof.
  intros x y f.
  apply hinhpr.
  simple refine (_ ,, _).
  - exact (η m x · pr111 f).
  - use eq_mor_kleisli_cat.
    cbn.
    rewrite functor_comp.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (!(pr211 f)).
    }
    cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply Monad_law2.
    }
    apply id_left.
Qed.

Definition faithful_functor_to_kleisli_cat
           {C : category}
           (m : Monad C)
  : faithful (functor_to_kleisli_cat m).
Proof.
  intros x y f.
  use invproofirrelevance.
  intros ψ₁ ψ₂.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  pose (pr2 ψ₁ @ !(pr2 ψ₂)) as p.
  cbn in p.
  pose (maponpaths (λ z, η m _ · pr111 z) p) as q.
  cbn in q.
  rewrite !assoc in q.
  refine (_ @ q @ _).
  - refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(nat_trans_ax (η m) _ _ (pr1 ψ₁))).
    }
    cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply Monad_law1.
    }
    apply id_right.
  - etrans.
    {
      apply maponpaths_2.
      exact (!(nat_trans_ax (η m) _ _ (pr1 ψ₂))).
    }
    cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply Monad_law1.
    }
    apply id_right.
Qed.

Definition fully_faithful_functor_to_kleisli_cat
           {C : category}
           (m : Monad C)
  : fully_faithful (functor_to_kleisli_cat m).
Proof.
  use full_and_faithful_implies_fully_faithful.
  split.
  - exact (full_functor_to_kleisli_cat m).
  - exact (faithful_functor_to_kleisli_cat m).
Defined.

Definition essentially_surjective_functor_to_kleisli_cat
           {C : category}
           (m : Monad C)
  : essentially_surjective (functor_to_kleisli_cat m).
Proof.
  intro x.
  induction x as [ x Hx ].
  revert Hx.
  use factor_dep_through_squash.
  - intro.
    apply isapropishinh.
  - intros Hx.
    apply hinhpr.
    refine (pr1 Hx ,, _).
    use z_iso_kleisli_cat.
    exact (pr2 Hx).
Defined.

(**
 4. The universal property
 *)
Section KleisliUMP1.
  Context {C₁ C₂ : univalent_category}
          (m : Monad C₁)
          (F : C₁ ⟶ C₂)
          (γ : m ∙ F ⟹ F)
          (p₁ : ∏ (x : C₁), #F (η m x) · γ x = identity _)
          (p₂ : ∏ (x : C₁), γ _ · γ x = #F (μ m x) · γ x).

  Definition functor_from_univalent_kleisli_cat
    : kleisli_cat m ⟶ C₂
    := lift_functor_along
         C₂
         (functor_to_kleisli_cat m)
         (essentially_surjective_functor_to_kleisli_cat m)
         (fully_faithful_functor_to_kleisli_cat m)
         (functor_from_kleisli_cat_monad m F γ p₁ p₂).

  Definition functor_from_univalent_kleisli_cat_nat_trans
    : kleisli_incl m ∙ functor_from_univalent_kleisli_cat ⟹ F
    := nat_trans_comp
         _ _ _
         (nat_trans_comp
            _ _ _
            (post_whisker
               (functor_to_kleisli_cat_incl_nat_z_iso m)
               functor_from_univalent_kleisli_cat)
            (pre_whisker
               _
               (lift_functor_along_comm
                  C₂
                  (functor_to_kleisli_cat m)
                  (essentially_surjective_functor_to_kleisli_cat m)
                  (fully_faithful_functor_to_kleisli_cat m)
                  (functor_from_kleisli_cat_monad m F γ p₁ p₂))))
         (functor_from_kleisli_cat_monad_nat_trans m F γ p₁ p₂).

  Definition functor_from_univalent_kleisli_cat_nat_trans_is_z_iso
    : is_nat_z_iso functor_from_univalent_kleisli_cat_nat_trans.
  Proof.
    unfold functor_from_univalent_kleisli_cat_nat_trans.
    use (@is_nat_z_iso_comp
             _ _ _ _ _
             _
             (functor_from_kleisli_cat_monad_nat_trans m F γ p₁ p₂)).
    - use (@is_nat_z_iso_comp
             _ _
             _
             (Left_Kleisli_functor m
              ∙ functor_to_kleisli_cat m
              ∙ functor_from_univalent_kleisli_cat)).
      + use post_whisker_z_iso_is_z_iso.
        apply (functor_to_kleisli_cat_incl_nat_z_iso m).
      + use (pre_whisker_on_nat_z_iso
               (Left_Kleisli_functor m)
               (lift_functor_along_comm C₂ (functor_to_kleisli_cat m)
                  (essentially_surjective_functor_to_kleisli_cat m)
                  (fully_faithful_functor_to_kleisli_cat m)
                  (functor_from_kleisli_cat_monad m F γ p₁ p₂))).
        apply (lift_functor_along_comm
                 C₂
                 (functor_to_kleisli_cat m)
                 (essentially_surjective_functor_to_kleisli_cat m)
                 (fully_faithful_functor_to_kleisli_cat m)
                 (functor_from_kleisli_cat_monad m F γ p₁ p₂)).
    - apply functor_from_kleisli_cat_monad_nat_trans_is_z_iso.
  Defined.

  Definition functor_from_univalent_kleisli_cat_eq
             (x : C₁)
    : functor_from_univalent_kleisli_cat_nat_trans (m x) · γ x
      =
      # functor_from_univalent_kleisli_cat (kleisli_nat_trans m x)
      · functor_from_univalent_kleisli_cat_nat_trans x.
  Proof.
    cbn -[lift_functor_along_comm functor_from_univalent_kleisli_cat].
    etrans.
    {
      apply maponpaths_2.
      apply id_right.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (_ @ functor_id _ _).
      apply maponpaths.
      use eq_mor_kleisli_cat.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (_ @ functor_id _ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      apply id_left.
    }
    pose (nat_trans_ax
             (lift_functor_along_comm
                C₂ (functor_to_kleisli_cat m)
                (essentially_surjective_functor_to_kleisli_cat m)
                (fully_faithful_functor_to_kleisli_cat m)
                (functor_from_kleisli_cat_monad m F γ p₁ p₂))
             (m x) x
             (kleisli_monad_nat_trans m x))
      as p.
    refine (_ @ p @ _).
    - apply maponpaths_2.
      refine (maponpaths (λ z, # _ z) _).
      use eq_mor_kleisli_cat.
      cbn.
      rewrite functor_id, id_left.
      apply idpath.
    - apply maponpaths.
      cbn.
      rewrite functor_id, id_left.
      apply idpath.
  Qed.
End KleisliUMP1.

Section KleisliUMP2.
  Context {C₁ C₂ : univalent_category}
          (m : Monad C₁)
          {G₁ G₂ : kleisli_cat m ⟶ C₂}
          (α : kleisli_incl m ∙ G₁ ⟹ kleisli_incl m ∙ G₂)
          (p : ∏ (x : C₁),
               #G₁ (kleisli_nat_trans m x) · α x
               =
               α (m x) · # G₂ (kleisli_nat_trans m x)).

  Definition nat_trans_from_univalent_kleisli_cat_help
    : Left_Kleisli_functor m ∙ (functor_to_kleisli_cat m ∙ G₁)
      ⟹
      Left_Kleisli_functor m ∙ (functor_to_kleisli_cat m ∙ G₂)
    := nat_trans_comp
         _ _ _
         (nat_trans_comp
            _ _ _
            (post_whisker
               (nat_z_iso_inv (functor_to_kleisli_cat_incl_nat_z_iso m))
               _)
            α)
         (post_whisker
            (functor_to_kleisli_cat_incl_nat_z_iso m)
            _).

  Definition nat_trans_from_univalent_kleisli_cat_help_eq
             (x : C₁)
    : # (functor_to_kleisli_cat m ∙ G₁) (kleisli_monad_nat_trans m x)
      · nat_trans_from_univalent_kleisli_cat_help x
      =
      nat_trans_from_univalent_kleisli_cat_help (m x)
      · # (functor_to_kleisli_cat m ∙ G₂) (kleisli_monad_nat_trans m x).
  Proof.
    refine (_ @ p x @ _).
    - cbn.
      rewrite !assoc.
      rewrite <- (functor_comp G₁).
      etrans.
      {
        apply maponpaths.
        refine (_  @ functor_id G₂ _).
        apply maponpaths.
        use subtypePath ; [ intro ; apply isapropunit | ].
        use eq_mor_eilenberg_moore.
        apply idpath.
      }
      rewrite id_right.
      apply maponpaths_2.
      apply maponpaths.
      use eq_mor_kleisli_cat.
      cbn.
      rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - cbn.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (_  @ functor_id G₁ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      rewrite id_left.
      rewrite <- (functor_comp G₂).
      do 2 apply maponpaths.
      use eq_mor_kleisli_cat.
      cbn.
      rewrite functor_id.
      rewrite !id_left.
      apply idpath.
  Qed.

  Definition nat_trans_from_univalent_kleisli_cat
    : G₁ ⟹ G₂
    := lift_nat_trans_along
         C₂
         (functor_to_kleisli_cat m)
         (essentially_surjective_functor_to_kleisli_cat m)
         (fully_faithful_functor_to_kleisli_cat m)
         (nat_trans_from_kleisli_cat_monad
            m
            nat_trans_from_univalent_kleisli_cat_help
            nat_trans_from_univalent_kleisli_cat_help_eq).

  Definition pre_whisker_nat_trans_from_univalent_kleisli_cat
    : pre_whisker _ nat_trans_from_univalent_kleisli_cat = α.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    pose (nat_trans_eq_pointwise
            (lift_nat_trans_along_comm
               C₂
               (functor_to_kleisli_cat m)
               (essentially_surjective_functor_to_kleisli_cat m)
               (fully_faithful_functor_to_kleisli_cat m)
               (nat_trans_from_kleisli_cat_monad
                  m
                  nat_trans_from_univalent_kleisli_cat_help
                  nat_trans_from_univalent_kleisli_cat_help_eq))
            x)
      as q.
    refine (q @ _).
    cbn.
    etrans.
    {
      apply maponpaths.
      refine (_  @ functor_id G₂ _).
      apply maponpaths.
      use eq_mor_kleisli_cat.
      apply idpath.
    }
    refine (id_right _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (_  @ functor_id G₁ _).
      apply maponpaths.
      use eq_mor_kleisli_cat.
      apply idpath.
    }
    apply id_left.
  Qed.

  Definition nat_trans_from_univalent_kleisli_cat_unique
             {β₁ β₂ : G₁ ⟹ G₂}
             (q₁ : pre_whisker _ β₁ = α)
             (q₂ : pre_whisker _ β₂ = α)
    : β₁ = β₂.
  Proof.
    use (lift_nat_trans_eq_along
             C₂
             (functor_to_kleisli_cat m)
             (essentially_surjective_functor_to_kleisli_cat m)
             (fully_faithful_functor_to_kleisli_cat m)).
    use (@nat_trans_from_kleisli_cat_monad_unique
             _ _
             m
             (functor_to_kleisli_cat m ∙ G₁)
             (functor_to_kleisli_cat m ∙ G₂)).
    - exact nat_trans_from_univalent_kleisli_cat_help.
    - use nat_trans_eq.
      {
        apply homset_property.
      }
      intro ; cbn.
      refine (nat_trans_eq_pointwise q₁ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (_  @ functor_id G₂ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (_  @ functor_id G₁ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      apply id_left.
    - use nat_trans_eq.
      {
        apply homset_property.
      }
      intro ; cbn.
      refine (nat_trans_eq_pointwise q₂ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (_  @ functor_id G₂ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (_  @ functor_id G₁ _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      apply id_left.
  Qed.
End KleisliUMP2.
