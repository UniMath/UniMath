(*****************************************************************************************

 The collage of a profunctor

 In this file, we define the collage (also know as the cograph) of profunctors. The collage
 of a profunctor `P : C₁ ↛ C₂` is defined as the following category:
 - objects: `C₁ ⨿ C₂`
 - morphisms from `x₁ : C₁` to `x₂ : C₁`: morphisms in `C₁`
 - morphisms from `x₁ : C₁` to `y₂ : C₂`: inhabitants of the empty type
 - morphisms from `y₁ : C₂` to `x₂ : C₁`: inhabitants of `P y₁ x₂`
 - morphisms from `y₁ : C₂` to `y₂ : C₂`: morphisms in `C₂`

 Content
 1. The collage of a profunctor
 2. The collage is univalent
 3. The inclusions into the collage
 4. The squares from the collage

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Squares.

Local Open Scope cat.

Section Collage.
  Context {C₁ C₂ : category}
          (P : C₁ ↛ C₂).

  (** * 1. The collage of a profunctor *)
  Definition collage_profunctor_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (C₁ ⨿ C₂).
    - intros x₁ x₂.
      induction x₁ as [ x₁ | y₁ ] ; induction x₂ as [ x₂ | y₂ ].
      + exact (x₁ --> x₂).
      + exact ∅.
      + exact (P y₁ x₂).
      + exact (y₁ --> y₂).
  Defined.

  Definition collage_profunctor_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact collage_profunctor_precategory_ob_mor.
    - intro x.
      induction x as [ x | y ].
      + exact (identity x).
      + exact (identity y).
    - intros x₁ x₂ x₃ f g.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        induction x₃ as [ x₃ | y₃ ] ;
        try (apply (fromempty f)) ;
        try (apply (fromempty g)) ;
        cbn in *.
      + exact (f · g).
      + exact (rmap P g f).
      + exact (lmap P f g).
      + exact (f · g).
  Defined.

  Proposition collage_profunctor_is_precategory
    : is_precategory collage_profunctor_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros x₁ x₂ f.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        try (apply (fromempty f)) ;
        cbn in *.
      + apply id_left.
      + apply lmap_id.
      + apply id_left.
    - intros x₁ x₂ f.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        try (apply (fromempty f)) ;
        cbn in *.
      + apply id_right.
      + apply rmap_id.
      + apply id_right.
    - intros x₁ x₂ x₃ x₄ f g h.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        induction x₃ as [ x₃ | y₃ ] ;
        induction x₄ as [ x₄ | y₄ ] ;
        try (apply (fromempty f)) ;
        try (apply (fromempty g)) ;
        try (apply (fromempty h)) ;
        cbn in *.
      + apply assoc.
      + apply rmap_comp.
      + apply lmap_rmap.
      + refine (!_).
        apply lmap_comp.
      + apply assoc.
  Qed.

  Definition collage_profunctor_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact collage_profunctor_precategory_data.
    - exact collage_profunctor_is_precategory.
  Defined.

  Proposition collage_profunctor_category_has_homsets
    : has_homsets collage_profunctor_precategory_ob_mor.
  Proof.
    intros x₁ x₂.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      cbn in *.
    - apply homset_property.
    - apply isasetempty.
    - apply setproperty.
    - apply homset_property.
  Qed.

  Definition collage_profunctor_category
    : category.
  Proof.
    use make_category.
    - exact collage_profunctor_precategory.
    - exact collage_profunctor_category_has_homsets.
  Defined.

  (** * 2. The collage is univalent *)
  Definition idtoiso_in_collage_inl
             {x₁ x₂ : C₁}
             (p : x₁ = x₂)
    : pr1 (idtoiso p)
      =
      pr1 (@idtoiso
             collage_profunctor_category
             (inl x₁)
             (inl x₂)
             (maponpaths inl p)).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition idtoiso_in_collage_inr
             {x₁ x₂ : C₂}
             (p : x₁ = x₂)
    : pr1 (idtoiso p)
      =
      pr1 (@idtoiso
             collage_profunctor_category
             (inr x₁)
             (inr x₂)
             (maponpaths inr p)).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition is_univalent_collage_profunctor_category
              (H₁ : is_univalent C₁)
              (H₂ : is_univalent C₂)
    : is_univalent collage_profunctor_category.
  Proof.
    intros x₁ x₂.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ].
    - use weqhomot.
      + exact (make_weq _ (H₁ _ _) ∘ paths_inl_inl_equiv _ _)%weq.
      + intro p ; cbn -[equality_by_case_equiv].
        use z_iso_eq.
        refine (idtoiso_in_collage_inl (paths_inl_inl_equiv x₁ x₂ p) @ _).
        do 2 apply maponpaths.
        apply (homotinvweqweq (paths_inl_inl_equiv _ _)).
    - use weqhomot.
      + refine (invweq _ ∘ paths_inl_inr_equiv _ _)%weq.
        use weqtoempty.
        intro f.
        exact (pr1 f).
      + intro p.
        use fromempty.
        exact (negpathsii1ii2 _ _ p).
    - use weqhomot.
      + refine (invweq _ ∘ paths_inr_inl_equiv _ _)%weq.
        use weqtoempty.
        intro f.
        exact (inv_from_z_iso f).
      + intro p.
        use fromempty.
        exact (negpathsii2ii1 _ _ p).
    - use weqhomot.
      + exact (make_weq _ (H₂ _ _) ∘ paths_inr_inr_equiv _ _)%weq.
      + intro p ; cbn -[equality_by_case_equiv].
        use z_iso_eq.
        refine (idtoiso_in_collage_inr (paths_inr_inr_equiv y₁ y₂ p) @ _).
        do 2 apply maponpaths.
        apply (homotinvweqweq (paths_inr_inr_equiv _ _)).
  Qed.

  (** * 3. The inclusions into the collage *)
  Definition collage_profunctor_category_inl_data
    : functor_data C₁ collage_profunctor_category.
  Proof.
    use make_functor_data.
    - exact inl.
    - exact (λ _ _ f, f).
  Defined.

  Definition collage_profunctor_category_inl
    : C₁ ⟶ collage_profunctor_category.
  Proof.
    use make_functor.
    - exact collage_profunctor_category_inl_data.
    - abstract
        (split ; intro ; intros ; apply idpath).
  Defined.

  Proposition collage_profunctor_category_inl_ff
    : fully_faithful collage_profunctor_category_inl.
  Proof.
    intros x y.
    apply idisweq.
  Defined.

  Definition collage_profunctor_category_inr_data
    : functor_data C₂ collage_profunctor_category.
  Proof.
    use make_functor_data.
    - exact inr.
    - exact (λ _ _ f, f).
  Defined.

  Definition collage_profunctor_category_inr
    : C₂ ⟶ collage_profunctor_category.
  Proof.
    use make_functor.
    - exact collage_profunctor_category_inr_data.
    - abstract
        (split ; intro ; intros ; apply idpath).
  Defined.

  Proposition collage_profunctor_category_inr_ff
    : fully_faithful collage_profunctor_category_inr.
  Proof.
    intros x y.
    apply idisweq.
  Defined.

  (** * 4. The squares from the collage *)
  Definition collage_profunctor_square
    : profunctor_square
        collage_profunctor_category_inr
        collage_profunctor_category_inl
        P
        (id_profunctor _).
  Proof.
    use make_profunctor_square.
    - exact (λ _ _ h, h).
    - abstract
        (intro ; intros ; cbn ;
         rewrite rmap_id ;
         rewrite lmap_id ;
         apply idpath).
  Defined.
End Collage.
