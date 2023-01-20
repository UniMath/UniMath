Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section TotalOfTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition total_twosided_disp_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (∑ (x : C₁) (y : C₂), D x y).
    - exact (λ xy₁ xy₂,
             ∑ (f : pr1 xy₁ --> pr1 xy₂)
               (g : pr12 xy₁ --> pr12 xy₂),
             pr22 xy₁ -->[ f ][ g ] pr22 xy₂).
  Defined.

  Definition total_twosided_disp_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact total_twosided_disp_precategory_ob_mor.
    - exact (λ xy,
             identity (pr1 xy)
             ,,
             identity (pr12 xy)
             ,,
             id_two_disp (pr22 xy)).
    - exact (λ xy₁ xy₂ xy₃ fg₁ fg₂,
             pr1 fg₁ · pr1 fg₂
             ,,
             pr12 fg₁ · pr12 fg₂
             ,,
             pr22 fg₁ ;;2 pr22 fg₂).
  Defined.

  Definition total_twosided_disp_is_precategory
    : is_precategory total_twosided_disp_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_left.
      + apply id_left.
      + apply id_two_disp_left.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_right.
      + apply id_right.
      + apply id_two_disp_right.
    - intros xy₁ xy₂ xy₃ xy₄ fg₁ fg₂ fg₃.
      use total2_paths_2_b.
      + apply assoc.
      + apply assoc.
      + apply assoc_two_disp.
  Qed.

  Definition total_twosided_disp_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact total_twosided_disp_precategory_data.
    - exact total_twosided_disp_is_precategory.
  Defined.

  Definition has_homsets_total_twosided_disp_category
    : has_homsets total_twosided_disp_precategory_ob_mor.
  Proof.
    intros xy₁ xy₂.
    apply isaset_total2.
    - apply homset_property.
    - intro.
      apply isaset_total2.
      + apply homset_property.
      + intro.
        apply isaset_disp_mor.
  Defined.

  Definition total_twosided_disp_category
    : category.
  Proof.
    use make_category.
    - exact total_twosided_disp_precategory.
    - exact has_homsets_total_twosided_disp_category.
  Defined.

  Definition from_eq_total
             {x₁ x₂ : total_twosided_disp_category}
             {f g : x₁ --> x₂}
             (p : f = g)
    : pr22 f
      =
      transportb
        (λ z, _ -->[ z ][ _ ] _)
        (maponpaths (λ z, pr1 z) p)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (maponpaths (λ z, pr12 z) p)
           (pr22 g)).
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition twosided_disp_category_pr1_data
    : functor_data total_twosided_disp_category C₁.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr1 xy).
    - exact (λ xy₁ xy₂ fg, pr1 fg).
  Defined.

  Definition twosided_disp_category_pr1_is_functor
    : is_functor twosided_disp_category_pr1_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr1
    : total_twosided_disp_category ⟶ C₁.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr1_data.
    - exact twosided_disp_category_pr1_is_functor.
  Defined.

  Definition twosided_disp_category_pr2_data
    : functor_data total_twosided_disp_category C₂.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr12 xy).
    - exact (λ xy₁ xy₂ fg, pr12 fg).
  Defined.

  Definition twosided_disp_category_pr2_is_functor
    : is_functor twosided_disp_category_pr2_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr2
    : total_twosided_disp_category ⟶ C₂.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr2_data.
    - exact twosided_disp_category_pr2_is_functor.
  Defined.

  Section IsoTotal.
    Context {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            {xy₁ : D x₁ y₁}
            {xy₂ : D x₂ y₂}
            {f : x₁ --> x₂}
            {Hf : is_z_isomorphism f}
            {g : y₁ --> y₂}
            {Hg : is_z_isomorphism g}
            (fg : xy₁ -->[ f ][ g ] xy₂)
            (Hfg : is_iso_twosided_disp Hf Hg fg).

    Let total_fg : total_twosided_disp_category ⟦ (x₁ ,, y₁ ,, xy₁) , (x₂ ,, y₂ ,, xy₂) ⟧
        := f ,, g ,, fg.
    Let f_z_iso : z_iso x₁ x₂ := f ,, Hf.
    Let g_z_iso : z_iso y₁ y₂ := g ,, Hg.

    Definition is_z_iso_total_twosided_disp_cat_inv
      : total_twosided_disp_category ⟦ (x₂ ,, y₂ ,, xy₂) , (x₁ ,, y₁ ,, xy₁) ⟧
      := inv_from_z_iso f_z_iso
         ,,
         inv_from_z_iso g_z_iso
         ,,
         iso_inv_twosided_disp Hfg.

    Definition is_z_iso_total_twosided_disp_cat_inv_right
      : total_fg · is_z_iso_total_twosided_disp_cat_inv = identity _.
    Proof.
      use total2_paths_2_b ; cbn.
      - apply (z_iso_inv_after_z_iso f_z_iso).
      - apply (z_iso_inv_after_z_iso g_z_iso).
      - apply inv_after_iso_twosided_disp.
    Qed.

    Definition is_z_iso_total_twosided_disp_cat_inv_left
      : is_z_iso_total_twosided_disp_cat_inv · total_fg = identity _.
    Proof.
      use total2_paths_2_b ; cbn.
      - apply (z_iso_after_z_iso_inv f_z_iso).
      - apply (z_iso_after_z_iso_inv g_z_iso).
      - apply iso_after_inv_twosided_disp.
    Qed.

    Definition is_z_iso_total_twosided_disp_cat
      : is_z_isomorphism total_fg.
    Proof.
      simple refine (is_z_iso_total_twosided_disp_cat_inv ,, _ ,, _).
      - apply is_z_iso_total_twosided_disp_cat_inv_right.
      - apply is_z_iso_total_twosided_disp_cat_inv_left.
    Defined.
  End IsoTotal.

  Definition make_z_iso_total_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             (fg : iso_twosided_disp f g xy₁ xy₂)
    : @z_iso
        total_twosided_disp_category
        (x₁ ,, y₁ ,, xy₁)
        (x₂ ,, y₂ ,, xy₂).
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 f ,, pr1 g ,, pr1 fg).
    - use is_z_iso_total_twosided_disp_cat.
      + exact (pr2 f).
      + exact (pr2 g).
      + exact (pr2 fg).
  Defined.

  Section FromIsoTotal.
      Context {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              (f : @z_iso
                     total_twosided_disp_category
                     (x₁ ,, y₁ ,, xy₁)
                     (x₂ ,, y₂ ,, xy₂)).

      Definition from_iso_total_twosided_disp_cat_pr1
        : z_iso x₁ x₂.
      Proof.
        use make_z_iso.
        - exact (pr11 f).
        - exact (pr1 (inv_from_z_iso f)).
        - split.
          + exact (maponpaths pr1 (z_iso_inv_after_z_iso f)).
          + exact (maponpaths pr1 (z_iso_after_z_iso_inv f)).
      Defined.

      Definition from_iso_total_twosided_disp_cat_pr12
        : z_iso y₁ y₂.
      Proof.
        use make_z_iso.
        - exact (pr121 f).
        - exact (pr12 (inv_from_z_iso f)).
        - split.
          + exact (maponpaths (λ z, pr12 z) (z_iso_inv_after_z_iso f)).
          + exact (maponpaths (λ z, pr12 z) (z_iso_after_z_iso_inv f)).
      Defined.

      Definition from_iso_total_twosided_disp_cat_pr22
        : iso_twosided_disp
            from_iso_total_twosided_disp_cat_pr1
            from_iso_total_twosided_disp_cat_pr12
            xy₁ xy₂.
      Proof.
        simple refine (_ ,, _ ,, _ ,, _).
        - exact (pr221 f).
        - exact (pr22 (inv_from_z_iso f)).
        - exact (from_eq_total (z_iso_inv_after_z_iso f)).
        - exact (from_eq_total (z_iso_after_z_iso_inv f)).
      Defined.

      Definition from_iso_total_twosided_disp_cat
        : ∑ (f : z_iso x₁ x₂)
            (g : z_iso y₁ y₂),
          iso_twosided_disp f g xy₁ xy₂.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact from_iso_total_twosided_disp_cat_pr1.
        - exact from_iso_total_twosided_disp_cat_pr12.
        - exact from_iso_total_twosided_disp_cat_pr22.
      Defined.
  End FromIsoTotal.

  Definition weq_z_iso_total_twosided_disp_cat_help_eq
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {fg₁ fg₂ : ∑ (f : z_iso x₁ x₂)
                          (g : z_iso y₁ y₂),
                        iso_twosided_disp f g xy₁ xy₂}
             (p : pr11 fg₁ = pr11 fg₂)
             (q : pr112 fg₁ = pr112 fg₂)
             (r : pr122 fg₁
                  =
                  transportb
                    (λ z, _ -->[ z ][ _ ] _)
                    p
                    (transportb
                       (λ z, _ -->[ _ ][ z ] _)
                       q
                       (pr122 fg₂)))
    : fg₁ = fg₂.
  Proof.
    induction fg₁ as [ f₁ fg₁ ].
    induction fg₁ as [ g₁ fg₁ ].
    induction f₁ as [ f₁ Hf₁ ].
    induction g₁ as [ g₁ Hg₁ ].
    induction fg₁ as [ fg₁ Hfg₁ ].
    induction fg₂ as [ f₂ fg₂ ].
    induction fg₂ as [ g₂ fg₂ ].
    induction f₂ as [ f₂ Hf₂ ].
    induction g₂ as [ g₂ Hg₂ ].
    induction fg₂ as [ fg₂ Hfg₂ ].
    cbn in *.
    induction p ; induction q ; cbn in *.
    induction r.
    assert (p : Hf₁ = Hf₂) by apply isaprop_is_z_isomorphism.
    induction p.
    apply maponpaths.
    assert (p : Hg₁ = Hg₂) by apply isaprop_is_z_isomorphism.
    induction p.
    do 2 apply maponpaths.
    apply isaprop_is_iso_twosided_disp.
  Qed.

  Definition weq_z_iso_total_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x₁ y₁)
             (xy₂ : D x₂ y₂)
    : (∑ (f : z_iso x₁ x₂)
         (g : z_iso y₁ y₂),
       iso_twosided_disp f g xy₁ xy₂)
      ≃
      (@z_iso
          total_twosided_disp_category
          (x₁ ,, y₁ ,, xy₁)
          (x₂ ,, y₂ ,, xy₂)).
  Proof.
    use weq_iso.
    - exact (λ fg, make_z_iso_total_twosided_disp_cat (pr22 fg)).
    - exact from_iso_total_twosided_disp_cat.
    - abstract
        (intros f ;
         use weq_z_iso_total_twosided_disp_cat_help_eq ; apply idpath).
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
         apply idpath).
  Defined.

  Definition is_univalent_total_twosided_disp_category
             (HC₁ : is_univalent C₁)
             (HC₂ : is_univalent C₂)
             (HD : is_univalent_twosided_disp_cat D)
    : is_univalent total_twosided_disp_category.
  Proof.
    intros x y.
    use weqhomot.
    - refine (weq_z_iso_total_twosided_disp_cat _ _
                     ∘ weqtotal2
                         (_ ,, HC₁ _ _)
                         (λ p,
                          weqtotal2
                            (_ ,, HC₂ _ _)
                            (λ q, (_ ,, HD _ _ _ _ p q _ _))
                          ∘ _
                          ∘ total2_paths_equiv _ _ _)
                     ∘ total2_paths_equiv _ _ _)%weq ; cbn.
      induction x, y.
      cbn in *.
      induction p.
      exact (idweq _).
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
         apply idpath).
  Qed.
End TotalOfTwoSidedDispCat.
