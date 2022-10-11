(******************************************************************************************

 Equalizers in the category of strict categories

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.

Definition equalizer_of_setcategory_precategory_ob_mor
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (∑ (x : C₁), F x = G x).
  - exact (λ x y, ∑ (f : pr1 x --> pr1 y),
           # F f · idtoiso (pr2 y)
           =
           idtoiso (pr2 x) · # G f).
Defined.

Definition equalizer_of_setcategory_precategory_data
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (equalizer_of_setcategory_precategory_ob_mor F G).
  - cbn ; refine (λ x, identity _ ,, _).
    abstract
      (rewrite !functor_id ;
       rewrite id_left, id_right ;
       apply idpath).
  - cbn ; refine (λ x y z f g, pr1 f · pr1 g ,, _).
    abstract
      (rewrite !functor_comp ;
       rewrite !assoc ;
       rewrite <- (pr2 f) ;
       rewrite !assoc' ;
       rewrite <- (pr2 g) ;
       apply idpath).
Defined.

Definition equalizer_of_setcategory_is_precategory
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : is_precategory (equalizer_of_setcategory_precategory_data F G).
Proof.
  use make_is_precategory_one_assoc ;
    intros ;
    (use subtypePath ; [ intro ; apply homset_property | ]) ;
    cbn.
  - apply id_left.
  - apply id_right.
  - apply assoc.
Qed.

Definition equalizer_of_setcategory_precategory
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : precategory.
Proof.
  use make_precategory.
  - exact (equalizer_of_setcategory_precategory_data F G).
  - exact (equalizer_of_setcategory_is_precategory F G).
Defined.

Definition equalizer_of_setcategory_is_setcategory
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : is_setcategory (equalizer_of_setcategory_precategory F G).
Proof.
  split.
  - use isaset_total2.
    + apply C₁.
    + intro.
      apply isasetaprop.
      exact (pr12 C₂ (F x) (G x)).
  - intros x y.
    use isaset_total2.
    + apply homset_property.
    + intro.
      apply isasetaprop.
      apply homset_property.
Qed.

Definition equalizer_of_setcategory
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : setcategory
  := equalizer_of_setcategory_precategory F G ,, equalizer_of_setcategory_is_setcategory F G.

Definition idtoiso_equalizer_of_setcategory
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {x y : equalizer_of_setcategory F G}
           (p : x = y)
  : pr11 (idtoiso p) = pr1 (idtoiso (maponpaths pr1 p)).
Proof.
  induction p.
  apply idpath.
Qed.

Definition equalizer_of_setcategory_pr1
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : equalizer_of_setcategory F G ⟶ C₁.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ x, pr1 x).
    + exact (λ x y f, pr1 f).
  - abstract (split ; intro ; intros ; apply idpath).
Defined.

Definition equalizer_of_setcategory_eq
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
  : equalizer_of_setcategory_pr1 F G ∙ F
    =
    equalizer_of_setcategory_pr1 F G ∙ G.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  use functor_data_eq ; cbn.
  - exact (λ x, pr2 x).
  - intros x y f.
    cbn.
    rewrite double_transport_idtoiso.
    rewrite !assoc'.
    rewrite (pr2 f).
    rewrite !assoc.
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
Qed.

Definition equalizer_of_setcategory_ump_mor_data
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {C₀ : setcategory}
           (H : C₀ ⟶ C₁)
           (p : H ∙ F = H ∙ G)
  : functor_data
      C₀
      (equalizer_of_setcategory F G).
Proof.
  use make_functor_data.
  - refine (λ x, H x ,, _).
    exact (maponpaths (λ z, pr11 z x) p).
  - refine (λ x y f, #H f ,, _).
    abstract
      (pose (from_eq_cat_of_setcategory p f) as q ;
       cbn in q ;
       etrans ;
         [ apply maponpaths_2 ;
           exact q
         | ] ;
       cbn ;
       rewrite !assoc' ;
       apply maponpaths ;
       refine (_ @ id_right _) ;
       apply maponpaths ;
       refine (!_) ;
       refine (_ @ pr1_idtoiso_concat
                 (maponpaths (λ z, pr11 z y) (!p))
                 (maponpaths (λ z, pr11 z y) p)) ;
       refine (!_) ;
       apply setcategory_refl_idtoiso).
Defined.

Definition equalizer_of_setcategory_ump_mor_is_functor
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {C₀ : setcategory}
           (H : C₀ ⟶ C₁)
           (p : H ∙ F = H ∙ G)
  : is_functor (equalizer_of_setcategory_ump_mor_data F G H p).
Proof.
  split.
  - intro x.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    apply functor_id.
  - intros x y z f g.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    apply functor_comp.
Qed.

Definition equalizer_of_setcategory_ump_mor
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {C₀ : setcategory}
           (H : C₀ ⟶ C₁)
           (p : H ∙ F = H ∙ G)
  : C₀ ⟶ equalizer_of_setcategory F G.
Proof.
  use make_functor.
  - exact (equalizer_of_setcategory_ump_mor_data F G H p).
  - exact (equalizer_of_setcategory_ump_mor_is_functor F G H p).
Defined.

Definition equalizer_of_setcategory_ump_mor_pr1
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {C₀ : setcategory}
           (H : C₀ ⟶ C₁)
           (p : H ∙ F = H ∙ G)
  : equalizer_of_setcategory_ump_mor F G H p ∙ equalizer_of_setcategory_pr1 F G
    =
    H.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  use functor_data_eq.
  - exact (λ _, idpath _).
  - exact (λ _ _ _, idpath _).
Qed.

Definition equalizer_of_setcategory_ump_unique
           {C₁ C₂ : setcategory}
           (F G : C₁ ⟶ C₂)
           {C₀ : setcategory}
           (H : C₀ ⟶ C₁)
           (p : H ∙ F = H ∙ G)
           (K : C₀ ⟶ equalizer_of_setcategory F G)
           (K_pr1 : K ∙ equalizer_of_setcategory_pr1 F G = H)
  : K = equalizer_of_setcategory_ump_mor F G H p.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  use functor_data_eq.
  - abstract
      (intro x ;
       use subtypePath ;
       [ intro z ;
         exact (pr12 C₂ (F z) (G z))
       | ] ;
       exact (maponpaths (λ z, pr11 z x) K_pr1)).
  - intros x₁ x₂ f.
    rewrite double_transport_idtoiso.
    rewrite !assoc'.
    use z_iso_inv_on_right.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    cbn.
    pose (from_eq_cat_of_setcategory K_pr1 f) as q.
    cbn in q.
    etrans.
    {
      apply maponpaths_2.
      exact q.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (idtoiso_equalizer_of_setcategory
                   F G
                   (equalizer_of_setcategory_ump_unique_subproof C₁ C₂ F G C₀ H p K K_pr1 x₂)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (maponpaths (λ z, (pr11 z) x₂)
                    (! K_pr1))).
      }
      etrans.
      {
        apply maponpaths.
        apply setcategory_refl_idtoiso.
      }
      apply id_right.
    }
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      exact (idtoiso_equalizer_of_setcategory
               F G
               (equalizer_of_setcategory_ump_unique_subproof C₁ C₂ F G C₀ H p K K_pr1 x₁)).
    }
    apply setcategory_eq_idtoiso.
Qed.

Definition cat_of_setcategory_equalizers
  : Equalizers cat_of_setcategory.
Proof.
  intros C₁ C₂ F G.
  use make_Equalizer.
  - exact (equalizer_of_setcategory F G).
  - exact (equalizer_of_setcategory_pr1 F G).
  - exact (equalizer_of_setcategory_eq F G).
  - use make_isEqualizer.
    intros C₀ H p.
    simple refine (_ ,, _).
    + refine (equalizer_of_setcategory_ump_mor F G H p ,, _).
      exact (equalizer_of_setcategory_ump_mor_pr1 F G H p).
    + abstract
        (simpl ;
         intro K ;
         use subtypePath ; [ intro ; apply cat_of_setcategory | ] ;
         apply equalizer_of_setcategory_ump_unique ;
         exact (pr2 K)).
Defined.
