(**********************************************************************************

 Fibers of two-sided displayed categories and two-sided fibrations

 In this file, we construct the fiber of two-sided displayed categories. Note that
 the constructions are similar to those for displayed categories. Again, we look at
 objects over given objects in the base and the morphisms are displayed morphisms
 over the identity. The difference is that we have to take the two-sidedness into
 account.

 We also show that if we have a discrete two-sided fibration, then every morphism
 in the base gives rise to a function between the fibers. Using that, we conclude
 that every discrete two-sided fibration gives rise to a profunctor.

 Contents
 1. Fiber set of a discrete two-sided fibration
 2. Fiber category of a two-sided fibration
 2.1. Definition of the fiber category
 2.2. Isos in the fiber
 2.3. Univalence of the fiber
 3. Fiber functor in a two-sided fibration

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

(**
 1. Fiber set of a discrete two-sided fibration
 *)
Definition fiber_hset_twosided_disp_cat
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (x : C₁)
           (y : C₂)
  : hSet.
Proof.
  use make_hSet.
  - exact (D x y).
  - exact (isaset_discrete_twosided_cat_ob HD x y).
Defined.

(**
 2. Fiber category of a two-sided fibration
 *)
Section FiberCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂)
          (x : C₁)
          (y : C₂).

  (**
   2.1. Definition of the fiber category
   *)
  Definition fiber_twosided_disp_precat_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (D x y).
    - exact (λ xy₁ xy₂, xy₁ -->[ identity x ][ identity y ] xy₂).
  Defined.

  Definition fiber_twosided_disp_precat_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact fiber_twosided_disp_precat_ob_mor.
    - exact (λ xy, id_two_disp xy).
    - exact (λ _ _ _ f g,
             transportf
               (λ z, _ -->[ z ][ _ ] _)
               (id_left _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (id_left _)
                  (f ;;2 g))).
  Defined.

  Definition fiber_twosided_disp_is_precategory
    : is_precategory fiber_twosided_disp_precat_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split.
    - intros xy₁ xy₂ f ; cbn.
      rewrite id_two_disp_left.
      unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
      rewrite !twosided_prod_transport.
      rewrite transport_f_f.
      use (transportf_set
             (λ z, xy₁ -->[ pr1 z ][ dirprod_pr2 z ] xy₂)
             (pathsdirprod _ _ @ pathsdirprod _ _)).
      apply isasetdirprod ; apply homset_property.
    - intros xy₁ xy₂ f ; cbn.
      rewrite id_two_disp_right.
      unfold transportb, transportb_disp_mor2, transportf_disp_mor2.
      rewrite !twosided_prod_transport.
      rewrite transport_f_f.
      use (transportf_set
             (λ z, xy₁ -->[ pr1 z ][ dirprod_pr2 z ] xy₂)
             (pathsdirprod _ _ @ pathsdirprod _ _)).
      apply isasetdirprod ; apply homset_property.
    - intros xy₁ xy₂ xy₃ xy₄ f g h ; cbn.
      rewrite two_disp_post_whisker_left.
      rewrite two_disp_post_whisker_right.
      rewrite two_disp_pre_whisker_left.
      rewrite two_disp_pre_whisker_right.
      rewrite assoc_two_disp.
      unfold transportb, transportb_disp_mor2, transportf_disp_mor2.
      rewrite !twosided_prod_transport.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply isasetdirprod ; apply homset_property.
  Qed.

  Definition fiber_twosided_disp_precat
    : precategory.
  Proof.
    use make_precategory.
    - exact fiber_twosided_disp_precat_data.
    - exact fiber_twosided_disp_is_precategory.
  Defined.

  Definition fiber_twosided_disp_cat
    : category.
  Proof.
    use make_category.
    - exact fiber_twosided_disp_precat.
    - intros xy₁ xy₂ ; cbn.
      apply isaset_disp_mor.
  Defined.

  (**
   2.2. Isos in the fiber
   *)
  Definition make_z_iso_in_fiber
             {xy₁ xy₂ : fiber_twosided_disp_cat}
             (f : z_iso xy₁ xy₂)
    : iso_twosided_disp (idtoiso (idpath x)) (idtoiso (idpath y)) xy₁ xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 f).
    - exact (inv_from_z_iso f).
    - abstract
        (cbn ;
         pose (p := z_iso_inv_after_z_iso f) ;
         cbn in p ;
         rewrite <- p ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite !twosided_swap_transport ;
         refine (!_) ;
         refine (transportbfinv (λ z, _ -->[ z ][ _ ] _) _ _ @ _) ;
         exact (transportbfinv (λ z, _ -->[ _ ][ z ] _) _ _)).
    - abstract
        (cbn ;
         pose (p := z_iso_after_z_iso_inv f) ;
         cbn in p ;
         rewrite <- p ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite !twosided_swap_transport ;
         refine (!_) ;
         refine (transportbfinv (λ z, _ -->[ z ][ _ ] _) _ _ @ _) ;
         exact (transportbfinv (λ z, _ -->[ _ ][ z ] _) _ _)).
  Defined.

  Definition from_z_iso_in_fiber
             {xy₁ xy₂ : fiber_twosided_disp_cat}
             (f : iso_twosided_disp (idtoiso (idpath x)) (idtoiso (idpath y)) xy₁ xy₂)
    : z_iso xy₁ xy₂.
  Proof.
    use make_z_iso.
    - exact (pr1 f).
    - exact (iso_inv_twosided_disp (pr2 f)).
    - split.
      + abstract
          (cbn ;
           pose (p := inv_after_iso_twosided_disp (pr2 f)) ;
           cbn in p ;
           rewrite p ;
           unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
           rewrite !twosided_swap_transport ;
           refine (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _ @ _) ;
           exact (transportfbinv (λ z, _ -->[ _ ][ z ] _) _ _)).
      + abstract
          (cbn ;
           pose (p := iso_after_inv_twosided_disp (pr2 f)) ;
           cbn in p ;
           rewrite p ;
           unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
           rewrite !twosided_swap_transport ;
           refine (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _ @ _) ;
           exact (transportfbinv (λ z, _ -->[ _ ][ z ] _) _ _)).
  Defined.

  Definition z_iso_in_fiber
             (xy₁ xy₂ : fiber_twosided_disp_cat)
    : iso_twosided_disp (idtoiso (idpath x)) (idtoiso (idpath y)) xy₁ xy₂
      ≃
      z_iso xy₁ xy₂.
  Proof.
    use weq_iso.
    - exact from_z_iso_in_fiber.
    - exact make_z_iso_in_fiber.
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
         apply idpath).
  Defined.

  (**
   2.3. Univalence of the fiber
   *)
  Definition is_univalent_fiber_twosided_disp_cat
             (HD : is_univalent_twosided_disp_cat D)
    : is_univalent fiber_twosided_disp_cat.
  Proof.
    intros xy₁ xy₂.
    use weqhomot.
    - exact (z_iso_in_fiber xy₁ xy₂
             ∘ make_weq _ (HD x x y y (idpath _) (idpath _) xy₁ xy₂))%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
         apply idpath).
  Defined.
End FiberCat.

(**
 3. Fiber functor in a two-sided fibration
 *)
Section TwoSidedDiscreteFibrationToProfunctor.
  Context {C₁ C₂ : category}
          (D : discrete_twosided_fibration C₁ C₂).

  Let HD : discrete_twosided_disp_cat D := pr12 D.
  Let HD' : is_discrete_twosided_fibration (pr12 D) := pr22 D.

  Definition fiber_fun_hset_twosided_disp_cat
             {x₁ x₂ : C₁}
             (f : x₁ --> x₂)
             {y₁ y₂ : C₂}
             (g : y₂ --> y₁)
    : fiber_hset_twosided_disp_cat HD x₂ y₂
      →
      fiber_hset_twosided_disp_cat HD x₁ y₁
    := λ xy,
       discrete_twosided_opcleaving_ob
         _
         (pr2 HD')
         (discrete_twosided_cleaving_ob
            _
            (pr1 HD')
            xy
            f)
         g.

  Definition discrete_twosided_fibration_to_profunctor_data
    : functor_data
        (category_binproduct C₁^op C₂)
        HSET.
  Proof.
    use make_functor_data.
    - exact (λ xy, fiber_hset_twosided_disp_cat HD (pr1 xy) (pr2 xy)).
    - exact (λ _ _ fg, fiber_fun_hset_twosided_disp_cat (pr1 fg) (pr2 fg)).
  Defined.

  Definition fiber_fun_hset_twosided_disp_cat_id_map
             {x : C₁}
             {y : C₂}
             (xy : fiber_hset_twosided_disp_cat HD x y)
  : fiber_fun_hset_twosided_disp_cat (identity x) (identity y) xy
    -->[ identity _ ][ identity _ ]
    xy.
  Proof.
    unfold fiber_fun_hset_twosided_disp_cat.
    use discrete_twosided_opcleaving_opcartesian.
    refine (transportb
              (λ z, _ -->[ z ][ _ ] _)
              _
              (transportb
                 (λ z, _ -->[ _ ][ z ] _)
                 _
                 (discrete_twosided_cleaving_mor _ (pr1 HD') xy (identity x)))).
    - exact (id_right _).
    - exact (id_right _).
  Defined.

  Definition fiber_fun_hset_twosided_disp_cat_id
             {x : C₁}
             {y : C₂}
             (xy : fiber_hset_twosided_disp_cat HD x y)
  : fiber_fun_hset_twosided_disp_cat (identity x) (identity y) xy
    =
    xy.
  Proof.
    use (mortoid_discrete_twosided_disp HD).
    exact (fiber_fun_hset_twosided_disp_cat_id_map xy).
  Qed.

  Definition fiber_fun_hset_twosided_disp_cat_comp_map
             {x₁ x₂ x₃ : C₁}
             (f₁ : x₃ --> x₂)
             (f₂ : x₂ --> x₁)
             {y₁ y₂ y₃ : C₂}
             (g₁ : y₁ --> y₂)
             (g₂ : y₂ --> y₃)
             (xy : fiber_hset_twosided_disp_cat HD x₁ y₁)
    : fiber_fun_hset_twosided_disp_cat (f₁ · f₂) (g₁ · g₂) xy
      -->[ identity _ ][ identity _ ]
      fiber_fun_hset_twosided_disp_cat
        f₁ g₂
        (fiber_fun_hset_twosided_disp_cat
           f₂ g₁
           xy).
  Proof.
    unfold fiber_fun_hset_twosided_disp_cat.
    use discrete_twosided_opcleaving_opcartesian.
    pose (h₁ := discrete_twosided_opcleaving_mor
                  _
                  (pr2 HD')
                  (discrete_twosided_cleaving_ob (pr1 D)
                     (pr1 HD')
                     (discrete_twosided_opcleaving_ob (pr1 D)
                        (pr2 HD')
                        (discrete_twosided_cleaving_ob (pr1 D) (pr1 HD') xy f₂) g₁)
                     f₁)
                  g₂).
    refine (transportb
              (λ z, _ -->[ _ ][ z ] _)
              (id_right _)
              (_ ;;2 h₁)).
    use discrete_twosided_cleaving_cartesian.
    pose (h₂ := discrete_twosided_opcleaving_mor
                  _
                  (pr2 HD')
                  (discrete_twosided_cleaving_ob (pr1 D) (pr1 HD') xy f₂) g₁).
    refine (transportb
              (λ z, _ -->[ z ][ _ ] _)
              (id_left _ @ !(id_right _))
              (transportb
                 (λ z, _ -->[ _ ][ z ] _)
                 (id_right _ @ !(id_left _))
                 (_ ;;2 h₂))).
    use discrete_twosided_cleaving_cartesian.
    pose (h₃ := discrete_twosided_cleaving_mor
                  _
                  (pr1 HD')
                  xy
                  (f₁ · f₂)).
    exact (transportb
             (λ z, _ -->[ _ ][ z ] _)
             (id_right _)
             h₃).
  Defined.

  Definition fiber_fun_hset_twosided_disp_cat_comp
             {x₁ x₂ x₃ : C₁}
             (f₁ : x₃ --> x₂)
             (f₂ : x₂ --> x₁)
             {y₁ y₂ y₃ : C₂}
             (g₁ : y₁ --> y₂)
             (g₂ : y₂ --> y₃)
             (xy : fiber_hset_twosided_disp_cat HD x₁ y₁)
    : fiber_fun_hset_twosided_disp_cat (f₁ · f₂) (g₁ · g₂) xy
      =
      fiber_fun_hset_twosided_disp_cat
        f₁ g₂
        (fiber_fun_hset_twosided_disp_cat
           f₂ g₁
           xy).
  Proof.
    use (mortoid_discrete_twosided_disp HD).
    exact (fiber_fun_hset_twosided_disp_cat_comp_map f₁ f₂ g₁ g₂ xy).
  Qed.

  Definition discrete_twosided_fibration_to_profunctor_is_functor
    : is_functor
        discrete_twosided_fibration_to_profunctor_data.
  Proof.
    repeat split.
    - intros z.
      use funextsec.
      exact fiber_fun_hset_twosided_disp_cat_id.
    - intros z₁ z₂ z₃ f g.
      use funextsec.
      exact (fiber_fun_hset_twosided_disp_cat_comp _ _ _ _).
  Qed.

  Definition discrete_twosided_fibration_to_profunctor
    : profunctor C₂ C₁.
  Proof.
    use make_functor.
    - exact discrete_twosided_fibration_to_profunctor_data.
    - exact discrete_twosided_fibration_to_profunctor_is_functor.
  Defined.
End TwoSidedDiscreteFibrationToProfunctor.
