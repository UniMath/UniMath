(************************************************************************************

 The product of 2-sided displayed categories

 Suppose that we have a 2-sided displayed category `D₁` from `C₁` to `C₃` and
 a 2-sided displayed category `D₂` from `C₂` to `C₄`. Then we obtain a 2-sided
 displayed category from `category_binproduct C₁ C₂` to `category_binproduct C₃ C₄`.
 The displayed objects and displayed morphisms are pairs of displayed objects and of
 displayed morphisms respectively.

 Contents
 1. The definition of the product of 2-sided displayed categories
 2. Isos in the product
 3. The univalence of the product

 ************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.

Section ProdTwoSidedDispCat.
  Context {C₁ C₂ C₃ C₄ : category}
          (D₁ : twosided_disp_cat C₁ C₃)
          (D₂ : twosided_disp_cat C₂ C₄).

  (**
   1. The definition of the product of 2-sided displayed categories
   *)
  Definition twosided_disp_cat_product_ob_mor
    : twosided_disp_cat_ob_mor
        (category_binproduct C₁ C₂)
        (category_binproduct C₃ C₄).
  Proof.
    simple refine (_ ,, _).
    - exact (λ wx yz, D₁ (pr1 wx) (pr1 yz) × D₂ (pr2 wx) (pr2 yz)).
    - exact (λ wx₁ wx₂ yz₁ yz₂ d₁ d₂ fg hk,
             pr1 d₁ -->[ pr1 fg ][ pr1 hk ] pr1 d₂
             ×
             pr2 d₁ -->[ pr2 fg ][ pr2 hk ] pr2 d₂).
  Defined.

  Definition twosided_disp_cat_product_id_comp
    : twosided_disp_cat_id_comp twosided_disp_cat_product_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ wx yz d,
             id_two_disp (pr1 d)
             ,,
             id_two_disp (pr2 d)).
    - exact (λ wx₁ wx₂ wx₃ yz₁ yz₂ yz₃ d₁ d₂ d₃ fg₁ fg₂ hk₁ hk₂ φ ψ,
             pr1 φ ;;2 pr1 ψ
             ,,
             pr2 φ ;;2 pr2 ψ).
  Defined.

  Definition twosided_disp_cat_product_data
    : twosided_disp_cat_data
        (category_binproduct C₁ C₂)
        (category_binproduct C₃ C₄).
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_product_ob_mor.
    - exact twosided_disp_cat_product_id_comp.
  Defined.

  Proposition transportf_twosided_disp_cat_product
              {wx₁ wx₂ : category_binproduct C₁ C₂}
              {yz₁ yz₂ : category_binproduct C₃ C₄}
              {d₁ : twosided_disp_cat_product_data wx₁ yz₁}
              {d₂ : twosided_disp_cat_product_data wx₂ yz₂}
              {fg fg' : wx₁ --> wx₂}
              (p : fg' = fg)
              {hk hk' : yz₁ --> yz₂}
              (q : hk' = hk)
              (φ : d₁ -->[ fg' ][ hk' ] d₂)
    : transportf_disp_mor2 p q φ
      =
      transportf_disp_mor2
        (maponpaths pr1 p) (maponpaths pr1 q)
        (pr1 φ)
      ,,
      transportf_disp_mor2
        (maponpaths dirprod_pr2 p) (maponpaths dirprod_pr2 q)
        (pr2 φ).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_twosided_disp_cat_product
              {wx₁ wx₂ : category_binproduct C₁ C₂}
              {yz₁ yz₂ : category_binproduct C₃ C₄}
              {d₁ : twosided_disp_cat_product_data wx₁ yz₁}
              {d₂ : twosided_disp_cat_product_data wx₂ yz₂}
              {fg fg' : wx₁ --> wx₂}
              (p : fg = fg')
              {hk hk' : yz₁ --> yz₂}
              (q : hk = hk')
              (φ : d₁ -->[ fg' ][ hk' ] d₂)
    : transportb_disp_mor2 p q φ
      =
      transportb_disp_mor2
        (maponpaths pr1 p) (maponpaths pr1 q)
        (pr1 φ)
      ,,
      transportb_disp_mor2
        (maponpaths dirprod_pr2 p) (maponpaths dirprod_pr2 q)
        (pr2 φ).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition twosided_disp_cat_product_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_product_data.
  Proof.
    repeat split.
    - intro ; intros.
      rewrite transportb_twosided_disp_cat_product.
      use pathsdirprod.
      + refine (id_two_disp_left _ @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
      + refine (id_two_disp_left _ @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
    - intro ; intros.
      rewrite transportb_twosided_disp_cat_product.
      use pathsdirprod.
      + refine (id_two_disp_right _ @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
      + refine (id_two_disp_right _ @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
    - intro ; intros.
      rewrite transportb_twosided_disp_cat_product.
      use pathsdirprod.
      + refine (assoc_two_disp _ _ _  @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
      + refine (assoc_two_disp _ _ _  @ _).
        apply transportb_disp_mor2_eq.
        apply idpath.
    - intro ; intros.
      apply isaset_dirprod.
      + apply isaset_disp_mor.
      + apply isaset_disp_mor.
  Qed.

  Definition twosided_disp_cat_product
    : twosided_disp_cat
        (category_binproduct C₁ C₂)
        (category_binproduct C₃ C₄).
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_product_data.
    - exact twosided_disp_cat_product_axioms.
  Defined.

  (**
   2. Isos in the product
   *)
  Definition is_isotwosided_disp_twosided_disp_cat_product
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             {fg : pr1 d₁ -->[ identity _ ][ identity _ ] pr1 d₂}
             (Hfg : is_iso_twosided_disp
                      (identity_is_z_iso (pr1 wx))
                      (identity_is_z_iso (pr1 yz))
                      fg)
             {hk : pr2 d₁ -->[ identity _ ][ identity _ ] pr2 d₂}
             (Hhk : is_iso_twosided_disp
                      (identity_is_z_iso (pr2 wx))
                      (identity_is_z_iso (pr2 yz))
                      hk)
    : @is_iso_twosided_disp
         _ _
         twosided_disp_cat_product
         _ _ _ _ _ _ _ _
         (identity_is_z_iso wx) (identity_is_z_iso yz)
         (fg ,, hk).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg ,, iso_inv_twosided_disp Hhk).
    - abstract
        (cbn ;
         rewrite transportb_twosided_disp_cat_product ;
         use dirprodeq ; cbn ;
         [ refine (inv_after_iso_twosided_disp Hfg @ _)
         | refine (inv_after_iso_twosided_disp Hhk @ _) ] ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite transportb_twosided_disp_cat_product ;
         use dirprodeq ; cbn ;
         [ refine (iso_after_inv_twosided_disp Hfg @ _)
         | refine (iso_after_inv_twosided_disp Hhk @ _) ] ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition twosided_disp_cat_product_iso_weq_map
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             (fg : iso_twosided_disp
                     (identity_z_iso (pr1 wx))
                     (identity_z_iso (pr1 yz))
                     (pr1 d₁) (pr1 d₂))
             (hk : iso_twosided_disp
                     (identity_z_iso (pr2 wx))
                     (identity_z_iso (pr2 yz))
                     (pr2 d₁) (pr2 d₂))
    : @iso_twosided_disp
         _ _
         twosided_disp_cat_product
         _ _ _ _
         (identity_z_iso wx) (identity_z_iso yz)
         d₁ d₂.
  Proof.
    use make_iso_twosided_disp.
    - exact (pr1 fg ,, pr1 hk).
    - apply is_isotwosided_disp_twosided_disp_cat_product.
      + apply fg.
      + apply hk.
  Defined.

  Definition is_twosided_disp_cat_iso_pr1
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             (φ : d₁ -->[ identity _ ][ identity _ ] d₂)
             (Hφ : @is_iso_twosided_disp
                      _ _
                      twosided_disp_cat_product
                      _ _ _ _ _ _
                      _ _
                      (identity_is_z_iso _) (identity_is_z_iso _)
                      φ)
    : is_iso_twosided_disp
        (identity_is_z_iso _) (identity_is_z_iso _)
        (pr1 φ).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (pr1 (iso_inv_twosided_disp Hφ)).
    - abstract
        (refine (maponpaths pr1 (inv_after_iso_twosided_disp Hφ) @ _) ;
         rewrite transportb_twosided_disp_cat_product ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (maponpaths pr1 (iso_after_inv_twosided_disp Hφ) @ _) ;
         rewrite transportb_twosided_disp_cat_product ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition twosided_disp_cat_product_iso_weq_inv_pr1
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             (φ : @iso_twosided_disp
                     _ _
                     twosided_disp_cat_product
                     _ _ _ _
                     (identity_z_iso wx) (identity_z_iso yz)
                     d₁ d₂)
    : iso_twosided_disp
        (identity_z_iso (pr1 wx))
        (identity_z_iso (pr1 yz))
        (pr1 d₁) (pr1 d₂).
  Proof.
    use make_iso_twosided_disp.
    - exact (pr11 φ).
    - apply is_twosided_disp_cat_iso_pr1.
      apply φ.
  Defined.

  Definition is_twosided_disp_cat_iso_pr2
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             (φ : d₁ -->[ identity _ ][ identity _ ] d₂)
             (Hφ : @is_iso_twosided_disp
                      _ _
                      twosided_disp_cat_product
                      _ _ _ _ _ _
                      _ _
                      (identity_is_z_iso _) (identity_is_z_iso _)
                      φ)
    : is_iso_twosided_disp
        (identity_is_z_iso _) (identity_is_z_iso _)
        (pr2 φ).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (pr2 (iso_inv_twosided_disp Hφ)).
    - abstract
        (refine (maponpaths dirprod_pr2 (inv_after_iso_twosided_disp Hφ) @ _) ;
         rewrite transportb_twosided_disp_cat_product ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (maponpaths dirprod_pr2 (iso_after_inv_twosided_disp Hφ) @ _) ;
         rewrite transportb_twosided_disp_cat_product ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition twosided_disp_cat_product_iso_weq_inv_pr2
             {wx : category_binproduct C₁ C₂}
             {yz : category_binproduct C₃ C₄}
             {d₁ d₂ : twosided_disp_cat_product_data wx yz}
             (φ : @iso_twosided_disp
                     _ _
                     twosided_disp_cat_product
                     _ _ _ _
                     (identity_z_iso wx) (identity_z_iso yz)
                     d₁ d₂)
    : iso_twosided_disp
        (identity_z_iso (pr2 wx))
        (identity_z_iso (pr2 yz))
        (pr2 d₁) (pr2 d₂).
  Proof.
    use make_iso_twosided_disp.
    - exact (pr21 φ).
    - apply is_twosided_disp_cat_iso_pr2.
      apply φ.
  Defined.

  Definition twosided_disp_cat_product_iso_weq
              {wx : category_binproduct C₁ C₂}
              {yz : category_binproduct C₃ C₄}
              (d₁ d₂ : twosided_disp_cat_product_data wx yz)
    : iso_twosided_disp
        (identity_z_iso (pr1 wx))
        (identity_z_iso (pr1 yz))
        (pr1 d₁) (pr1 d₂)
      ×
      iso_twosided_disp
        (identity_z_iso (pr2 wx))
        (identity_z_iso (pr2 yz))
        (pr2 d₁) (pr2 d₂)
      ≃
      @iso_twosided_disp
         _ _
         twosided_disp_cat_product
         _ _ _ _
         (identity_z_iso wx) (identity_z_iso yz)
         d₁ d₂.
  Proof.
    use weq_iso.
    - exact (λ fghk, twosided_disp_cat_product_iso_weq_map (pr1 fghk) (pr2 fghk)).
    - exact (λ φ,
             twosided_disp_cat_product_iso_weq_inv_pr1 φ
             ,,
             twosided_disp_cat_product_iso_weq_inv_pr2 φ).
    - abstract
        (intros fghk ;
         use dirprodeq ;
         (use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ]) ;
         apply idpath).
    - abstract
        (intros φ ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  (**
   3. The univalence of the product
   *)
  Proposition is_univalent_twosided_disp_cat_product
              (HD₁ : is_univalent_twosided_disp_cat D₁)
              (HD₂ : is_univalent_twosided_disp_cat D₂)
    : is_univalent_twosided_disp_cat twosided_disp_cat_product.
  Proof.
    intros wx₁ wx₂ yz₁ yz₂ p q d₁ d₂.
    induction p, q.
    use weqhomot.
    - exact (twosided_disp_cat_product_iso_weq d₁ d₂
             ∘ weqdirprodf
                 (make_weq
                    _
                    (HD₁ _ _ _ _ (idpath (pr1 wx₁)) (idpath (pr1 yz₁)) (pr1 d₁) (pr1 d₂)))
                 (make_weq
                    _
                    (HD₂ _ _ _ _ (idpath (pr2 wx₁)) (idpath (pr2 yz₁)) (pr2 d₁) (pr2 d₂)))
             ∘ pathsdirprodweq)%weq.
    - abstract
        (intro p ; cbn in p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.
End ProdTwoSidedDispCat.
