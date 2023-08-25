(**********************************************************************************

 Total categories

 We prove that every two-sided displayed category gives rise to a span of
 categories. More specifically, every two-sided displayed category `D` over `C₁`
 and `C₂` gives rise to a total category `∫ D`, a first projection `∫ D ⟶ C₁`, and
 a second projection `∫ D ⟶ C₂`. In addition, the univalence of `∫ D` follows from
 the displayed univalence of `D` and the univalence of both `C₁` and `D₂`.

 Note that we can also construct total displayed categories from a two-sided
 displayed category. More specifically, if we have a two-sided displayed category
 `D` over `C₁` and `C₂`, then we get the left total displayed category over `C₂`
 and the right total displayed category over `C₁`. Univalence of those displayed
 categories follows from the univalence of `D`.

 Contents
 1. Total category
 1.1. Definition
 1.2. First and second projection
 1.3. Isos in the total category
 1.4. Univalence of the total category
 2. Left total displayed category
 2.1. Definition
 2.2. Isomorphisms
 2.3. The univalence
 3. Right total displayed category
 3.1. Definition
 3.2. Isomorphisms
 3.3. The univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.

Definition transportb_total2
           {X Y : UU}
           (Z : X → Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           (yz : ∑ (y : Y), Z x₂ y)
  : transportb
      (λ (x : X), ∑ (y : Y), Z x y)
      p
      yz
    =
    pr1 yz
    ,,
    transportb
      (λ x, Z x (pr1 yz))
      p
      (pr2 yz).
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Section TotalOfTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  (**
   1. Total category
   *)

  (**
   1.1. Definition
   *)
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

  (**
   1.2. First and second projection
   *)
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

  (**
   1.3. Isos in the total category
   *)
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

  (**
   1.4. Univalence of the total category
   *)
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

  (**
   2. Left total displayed category
   *)

  (**
   2.1. Definition
   *)
  Definition left_total_of_twosided_disp_cat_ob_mor
    : disp_cat_ob_mor C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ y, ∑ (x : C₁), D x y).
    - exact (λ y₁ y₂ xy₁ xy₂ g,
             ∑ (f : pr1 xy₁ --> pr1 xy₂),
             pr2 xy₁ -->[ f ][ g ] pr2 xy₂).
  Defined.

  Definition left_total_of_twosided_disp_cat_id_comp
    : disp_cat_id_comp C₂ left_total_of_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ y xy, identity (pr1 xy) ,, id_two_disp (pr2 xy)).
    - exact (λ y₁ y₂ y₃ g₁ g₂ xy₁ xy₂ xy₃ fg₁ fg₂,
             pr1 fg₁ · pr1 fg₂
             ,,
             (pr2 fg₁ ;;2 pr2 fg₂)).
  Defined.

  Definition left_total_of_twosided_disp_cat_data
    : disp_cat_data C₂.
  Proof.
    simple refine (_ ,, _).
    - exact left_total_of_twosided_disp_cat_ob_mor.
    - exact left_total_of_twosided_disp_cat_id_comp.
  Defined.

  Definition left_total_of_twosided_disp_cat_axioms
    : disp_cat_axioms C₂ left_total_of_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply id_left.
      + cbn.
        rewrite id_two_disp_left.
        unfold transportb_disp_mor2, transportf_disp_mor2.
        apply (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _).
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply id_right.
      + cbn.
        rewrite id_two_disp_right.
        apply (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _).
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply assoc.
      + cbn.
        rewrite assoc_two_disp.
        apply (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _).
    - intros.
      apply isaset_total2.
      + apply homset_property.
      + intro.
        apply isaset_disp_mor.
  Qed.

  Definition left_total_of_twosided_disp_cat
    : disp_cat C₂.
  Proof.
    simple refine (_ ,, _).
    - exact left_total_of_twosided_disp_cat_data.
    - exact left_total_of_twosided_disp_cat_axioms.
  Defined.

  (**
   2.2. Isomorphisms
   *)
  Definition make_iso_left_total_of_twosided_disp_cat
             {y : C₂}
             {xy₁ xy₂ : left_total_of_twosided_disp_cat y}
             (f : z_iso (pr1 xy₁) (pr1 xy₂))
             (fg : iso_twosided_disp f (identity_z_iso _) (pr2 xy₁) (pr2 xy₂))
    : z_iso_disp (identity_z_iso _) xy₁ xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 f ,, pr1 fg).
    - exact (pr12 f ,, pr12 fg).
    - abstract
        (unfold mor_disp ; cbn ;
         rewrite transportb_total2 ; cbn ;
         use total2_paths_f ; [ apply z_iso_after_z_iso_inv | ] ;
         cbn ;
         etrans ; [ apply maponpaths ; apply (iso_after_inv_twosided_disp (pr2 fg)) | ] ;
         apply (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _)).
    - abstract
        (unfold mor_disp ; cbn ;
         rewrite transportb_total2 ; cbn ;
         use total2_paths_f ; [ apply z_iso_inv_after_z_iso | ] ;
         cbn ;
         etrans ; [ apply maponpaths ; apply (inv_after_iso_twosided_disp (pr2 fg)) | ] ;
         apply (transportfbinv (λ z, _ -->[ z ][ _ ] _) _ _)).
  Defined.

  Definition from_iso_left_total_of_twosided_disp_cat_pr1
             {y : C₂}
             {xy₁ xy₂ : left_total_of_twosided_disp_cat y}
             (f : z_iso_disp (identity_z_iso _) xy₁ xy₂)
    : z_iso (pr1 xy₁) (pr1 xy₂).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr11 f).
    - exact (pr112 f).
    - abstract
        (refine (maponpaths pr1 (inv_mor_after_z_iso_disp f) @ _) ;
         unfold mor_disp ; cbn ;
         rewrite transportb_total2 ;
         apply idpath).
    - abstract
        (refine (maponpaths pr1 (z_iso_disp_after_inv_mor f) @ _) ;
         unfold mor_disp ; cbn ;
         rewrite transportb_total2 ;
         apply idpath).
  Defined.

  Definition from_iso_left_total_of_twosided_disp_cat_pr2
             {y : C₂}
             {xy₁ xy₂ : left_total_of_twosided_disp_cat y}
             (f : z_iso_disp (identity_z_iso _) xy₁ xy₂)
    : iso_twosided_disp
        (from_iso_left_total_of_twosided_disp_cat_pr1 f)
        (identity_z_iso _) (pr2 xy₁) (pr2 xy₂).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr21 f).
    - exact (pr212 f).
    - abstract
        (pose (p := inv_mor_after_z_iso_disp f) ; unfold mor_disp in p ; cbn in p ;
         rewrite transportb_total2 in p ;
         refine (!(fiber_paths (!p)) @ _) ; cbn ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite !twosided_prod_transport ;
         apply maponpaths_2 ;
         apply isaset_dirprod ; apply homset_property).
    - abstract
        (pose (p := z_iso_disp_after_inv_mor f) ; unfold mor_disp in p ; cbn in p ;
         rewrite transportb_total2 in p ;
         refine (!(fiber_paths (!p)) @ _) ; cbn ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite !twosided_prod_transport ;
         apply maponpaths_2 ;
         apply isaset_dirprod ; apply homset_property).
  Defined.

  Definition weq_iso_left_total_of_twosided_disp_cat_eq_help
             {y : C₂}
             {xy₁ xy₂ : left_total_of_twosided_disp_cat y}
             {fg₁ fg₂ : ∑ (f : z_iso (pr1 xy₁) (pr1 xy₂)),
                        iso_twosided_disp
                          f (identity_z_iso _)
                          (pr2 xy₁) (pr2 xy₂)}
             (p : pr11 fg₁ = pr11 fg₂)
             (q : pr12 fg₁
                  =
                  transportb
                    (λ z, _ -->[ z ][ _ ] _)
                    p
                    (pr12 fg₂))
    : fg₁ = fg₂.
  Proof.
    induction fg₁ as [ f₁ fg₁ ].
    induction f₁ as [ f₁ Hf₁ ].
    induction fg₁ as [ fg₁ Hfg₁ ].
    induction fg₂ as [ f₂ fg₂ ].
    induction f₂ as [ f₂ Hf₂ ].
    induction fg₂ as [ fg₂ Hfg₂ ].
    cbn in *.
    induction p ; cbn in *.
    induction q.
    assert (Hf₁ = Hf₂) as p by apply isaprop_is_z_isomorphism.
    induction p.
    do 2 apply maponpaths.
    apply isaprop_is_iso_twosided_disp.
  Qed.

  Definition weq_iso_left_total_of_twosided_disp_cat
             {y : C₂}
             (xy₁ xy₂ : left_total_of_twosided_disp_cat y)
    : (∑ (f : z_iso (pr1 xy₁) (pr1 xy₂)),
       iso_twosided_disp f (identity_z_iso _) (pr2 xy₁) (pr2 xy₂))
      ≃
      z_iso_disp (identity_z_iso _) xy₁ xy₂.
  Proof.
    use weq_iso.
    - exact (λ f, make_iso_left_total_of_twosided_disp_cat (pr1 f) (pr2 f)).
    - exact (λ f,
             from_iso_left_total_of_twosided_disp_cat_pr1 f
             ,,
             from_iso_left_total_of_twosided_disp_cat_pr2 f).
    - abstract
        (intro f ;
         cbn ;
         use weq_iso_left_total_of_twosided_disp_cat_eq_help ;
         apply idpath).
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply idpath).
  Defined.

  (**
   2.3. The univalence
   *)
  Definition is_univalent_left_total_of_twosided_disp_cat
             (HC₁ : is_univalent C₁)
             (HD : is_univalent_twosided_disp_cat D)
    : is_univalent_disp left_total_of_twosided_disp_cat.
  Proof.
    intros y₁ y₂ p xy₁ xy₂.
    induction p.
    use weqhomot.
    - exact (weq_iso_left_total_of_twosided_disp_cat xy₁ xy₂
             ∘ weqtotal2
                 (_ ,, HC₁ _ _)
                 (λ p, (_ ,, HD _ _ _ _ p (idpath _) (pr2 xy₁) (pr2 xy₂)))
             ∘ total2_paths_equiv _ _ _)%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         apply idpath).
  Defined.

  (**
   3. Right total displayed category
   *)

  (**
   3.1. Definition
   *)
  Definition right_total_of_twosided_disp_cat_ob_mor
    : disp_cat_ob_mor C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, ∑ (y : C₂), D x y).
    - exact (λ x₁ x₂ xy₁ xy₂ f,
             ∑ (g : pr1 xy₁ --> pr1 xy₂),
             pr2 xy₁ -->[ f ][ g ] pr2 xy₂).
  Defined.

  Definition right_total_of_twosided_disp_cat_id_comp
    : disp_cat_id_comp C₁ right_total_of_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x xy, identity (pr1 xy) ,, id_two_disp (pr2 xy)).
    - exact (λ x₁ x₂ x₃ f₁ f₂ xy₁ xy₂ xy₃ fg₁ fg₂,
             pr1 fg₁ · pr1 fg₂
             ,,
             (pr2 fg₁ ;;2 pr2 fg₂)).
  Defined.

  Definition right_total_of_twosided_disp_cat_data
    : disp_cat_data C₁.
  Proof.
    simple refine (_ ,, _).
    - exact right_total_of_twosided_disp_cat_ob_mor.
    - exact right_total_of_twosided_disp_cat_id_comp.
  Defined.

  Definition right_total_of_twosided_disp_cat_axioms
    : disp_cat_axioms C₁ right_total_of_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply id_left.
      + cbn.
        rewrite id_two_disp_left.
        unfold transportb, transportb_disp_mor2, transportf_disp_mor2.
        rewrite <- twosided_swap_transport.
        apply transportfbinv.
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply id_right.
      + cbn.
        rewrite id_two_disp_right.
        unfold transportb, transportb_disp_mor2, transportf_disp_mor2.
        rewrite <- twosided_swap_transport.
        apply transportfbinv.
    - intro ; intros.
      unfold mor_disp ; cbn.
      rewrite transportb_total2.
      use total2_paths_f.
      + apply assoc.
      + cbn.
        rewrite assoc_two_disp.
        unfold transportb, transportb_disp_mor2, transportf_disp_mor2.
        rewrite <- twosided_swap_transport.
        apply transportfbinv.
    - intros.
      apply isaset_total2.
      + apply homset_property.
      + intro.
        apply isaset_disp_mor.
  Qed.

  Definition right_total_of_twosided_disp_cat
    : disp_cat C₁.
  Proof.
    simple refine (_ ,, _).
    - exact right_total_of_twosided_disp_cat_data.
    - exact right_total_of_twosided_disp_cat_axioms.
  Defined.

  (**
   3.2. Isomorphisms
   *)
  Definition make_iso_right_total_of_twosided_disp_cat
             {x : C₁}
             {xy₁ xy₂ : right_total_of_twosided_disp_cat x}
             (g : z_iso (pr1 xy₁) (pr1 xy₂))
             (fg : iso_twosided_disp (identity_z_iso _) g (pr2 xy₁) (pr2 xy₂))
    : z_iso_disp (identity_z_iso _) xy₁ xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 g ,, pr1 fg).
    - exact (pr12 g ,, pr12 fg).
    - abstract
        (unfold mor_disp ; cbn ;
         rewrite transportb_total2 ; cbn ;
         use total2_paths_f ; [ apply z_iso_after_z_iso_inv | ] ;
         cbn ;
         etrans ; [ apply maponpaths ; apply (iso_after_inv_twosided_disp (pr2 fg)) | ] ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite <- twosided_swap_transport ;
         apply transportfbinv).
    - abstract
        (unfold mor_disp ; cbn ;
         rewrite transportb_total2 ; cbn ;
         use total2_paths_f ; [ apply z_iso_inv_after_z_iso | ] ;
         cbn ;
         etrans ; [ apply maponpaths ; apply (inv_after_iso_twosided_disp (pr2 fg)) | ] ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite <- twosided_swap_transport ;
         apply transportfbinv).
  Defined.

  Definition from_iso_right_total_of_twosided_disp_cat_pr1
             {x : C₁}
             {xy₁ xy₂ : right_total_of_twosided_disp_cat x}
             (g : z_iso_disp (identity_z_iso _) xy₁ xy₂)
    : z_iso (pr1 xy₁) (pr1 xy₂).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr11 g).
    - exact (pr112 g).
    - abstract
        (refine (maponpaths pr1 (inv_mor_after_z_iso_disp g) @ _) ;
         unfold mor_disp ; cbn ;
         rewrite transportb_total2 ;
         apply idpath).
    - abstract
        (refine (maponpaths pr1 (z_iso_disp_after_inv_mor g) @ _) ;
         unfold mor_disp ; cbn ;
         rewrite transportb_total2 ;
         apply idpath).
  Defined.

  Definition from_iso_right_total_of_twosided_disp_cat_pr2
             {x : C₁}
             {xy₁ xy₂ : right_total_of_twosided_disp_cat x}
             (g : z_iso_disp (identity_z_iso _) xy₁ xy₂)
    : iso_twosided_disp
        (identity_z_iso _)
        (from_iso_right_total_of_twosided_disp_cat_pr1 g)
        (pr2 xy₁) (pr2 xy₂).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr21 g).
    - exact (pr212 g).
    - abstract
        (pose (p := inv_mor_after_z_iso_disp g) ; unfold mor_disp in p ; cbn in p ;
         rewrite transportb_total2 in p ;
         refine (!(fiber_paths (!p)) @ _) ; cbn ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite twosided_swap_transport ;
         rewrite !twosided_prod_transport ;
         apply maponpaths_2 ;
         apply isaset_dirprod ; apply homset_property).
    - abstract
        (pose (p := z_iso_disp_after_inv_mor g) ; unfold mor_disp in p ; cbn in p ;
         rewrite transportb_total2 in p ;
         refine (!(fiber_paths (!p)) @ _) ; cbn ;
         unfold transportb, transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite twosided_swap_transport ;
         rewrite !twosided_prod_transport ;
         apply maponpaths_2 ;
         apply isaset_dirprod ; apply homset_property).
  Defined.

  Definition weq_iso_right_total_of_twosided_disp_cat_eq_help
             {x : C₁}
             {xy₁ xy₂ : right_total_of_twosided_disp_cat x}
             {fg₁ fg₂ : ∑ (g : z_iso (pr1 xy₁) (pr1 xy₂)),
                        iso_twosided_disp
                          (identity_z_iso _)
                          g
                          (pr2 xy₁) (pr2 xy₂)}
             (p : pr11 fg₁ = pr11 fg₂)
             (q : pr12 fg₁
                  =
                  transportb
                    (λ z, _ -->[ _ ][ z ] _)
                    p
                    (pr12 fg₂))
    : fg₁ = fg₂.
  Proof.
    induction fg₁ as [ f₁ fg₁ ].
    induction f₁ as [ f₁ Hf₁ ].
    induction fg₁ as [ fg₁ Hfg₁ ].
    induction fg₂ as [ f₂ fg₂ ].
    induction f₂ as [ f₂ Hf₂ ].
    induction fg₂ as [ fg₂ Hfg₂ ].
    cbn in *.
    induction p ; cbn in *.
    induction q.
    assert (Hf₁ = Hf₂) as p by apply isaprop_is_z_isomorphism.
    induction p.
    do 2 apply maponpaths.
    apply isaprop_is_iso_twosided_disp.
  Qed.

  Definition weq_iso_right_total_of_twosided_disp_cat
             {x : C₁}
             (xy₁ xy₂ : right_total_of_twosided_disp_cat x)
    : (∑ (g : z_iso (pr1 xy₁) (pr1 xy₂)),
       iso_twosided_disp (identity_z_iso _) g (pr2 xy₁) (pr2 xy₂))
      ≃
      z_iso_disp (identity_z_iso _) xy₁ xy₂.
  Proof.
    use weq_iso.
    - exact (λ f, make_iso_right_total_of_twosided_disp_cat (pr1 f) (pr2 f)).
    - exact (λ f,
             from_iso_right_total_of_twosided_disp_cat_pr1 f
             ,,
             from_iso_right_total_of_twosided_disp_cat_pr2 f).
    - abstract
        (intro f ;
         cbn ;
         use weq_iso_right_total_of_twosided_disp_cat_eq_help ;
         apply idpath).
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply idpath).
  Defined.

  (**
   3.3. The univalence
   *)
  Definition is_univalent_right_total_of_twosided_disp_cat
             (HC₂ : is_univalent C₂)
             (HD : is_univalent_twosided_disp_cat D)
    : is_univalent_disp right_total_of_twosided_disp_cat.
  Proof.
    intros y₁ y₂ p xy₁ xy₂.
    induction p.
    use weqhomot.
    - exact (weq_iso_right_total_of_twosided_disp_cat xy₁ xy₂
             ∘ weqtotal2
                 (_ ,, HC₂ _ _)
                 (λ q, (_ ,, HD _ _ _ _ (idpath _) q (pr2 xy₁) (pr2 xy₂)))
             ∘ total2_paths_equiv _ _ _)%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         apply idpath).
  Defined.
End TotalOfTwoSidedDispCat.
