(**********************************************************************************

 The constant two-sided displayed category

 Given categories `C₁, C₂, D`, we define the constant two-sided displayed category
 over `C₁` and `C₂` as follows: the displayed objects are objects in `D` while the
 displayed morphisms are morphisms in `D`.

 Contents
 1. Definition via two-sided displayed categories
 2. Isomorphisms
 3. Univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.

Section ConstantTwoSidedDispCat.
  Context (C₁ C₂ D : category).

  (**
   1. Definition via two-sided displayed categories
   *)
  Definition constant_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, D).
    - exact (λ _ _ _ _ z₁ z₂ _ _, z₁ --> z₂).
  Defined.

  Definition constant_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp constant_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ _, identity _).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂, h₁ · h₂).
  Defined.

  Definition constant_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact constant_twosided_disp_cat_ob_mor.
    - exact constant_twosided_disp_cat_id_comp.
  Defined.

  Definition constant_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms constant_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply id_left.
    - intro ; intros ; unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply id_right.
    - intro ; intros ; unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply assoc.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition constant_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact constant_twosided_disp_cat_data.
    - exact constant_twosided_disp_cat_axioms.
  Defined.

  (**
   2. Isomorphisms
   *)
  Definition to_is_twosided_disp_cat_iso_constant
             (x : C₁)
             (y : C₂)
             {z₁ z₂ : D}
             (f : z₁ --> z₂)
             (Hf : is_z_isomorphism f)
    : @is_iso_twosided_disp
        _ _
        constant_twosided_disp_cat
        _ _ _ _
        _ _
        _ _
        (identity_is_z_iso x)
        (identity_is_z_iso y)
        f.
  Proof.
    pose (f_iso := (f ,, Hf) : z_iso _ _).
    simple refine (_ ,, _ ,, _).
    - exact (inv_from_z_iso f_iso).
    - abstract
        (cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_const ;
         apply Hf).
    - abstract
        (cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_const ;
         apply Hf).
  Defined.

  Definition z_iso_to_twosided_disp_cat_iso
             (x : C₁)
             (y : C₂)
             {z₁ z₂ : D}
             (f : z_iso z₁ z₂)
    : @iso_twosided_disp
        _ _
        constant_twosided_disp_cat
        _ _ _ _
        (identity_z_iso x) (identity_z_iso y)
        z₁ z₂.
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 f).
    - apply to_is_twosided_disp_cat_iso_constant.
      exact (pr2 f).
  Defined.

  Definition twosided_disp_cat_iso_to_z_iso
             (x : C₁)
             (y : C₂)
             {z₁ z₂ : D}
             (f : @iso_twosided_disp
                    _ _
                    constant_twosided_disp_cat
                    _ _ _ _
                    (identity_z_iso x) (identity_z_iso y)
                    z₁ z₂)
    : z_iso z₁ z₂.
  Proof.
    use make_z_iso.
    - exact (pr1 f).
    - exact (pr12 f).
    - split.
      + abstract
          (pose (p := pr122 f) ; cbn in p ;
           unfold transportb_disp_mor2, transportf_disp_mor2 in p ;
           cbn in p ;
           rewrite !transportf_const in p ;
           exact p).
      + abstract
          (pose (p := pr222 f) ; cbn in p ;
           unfold transportb_disp_mor2, transportf_disp_mor2 in p ;
           cbn in p ;
           rewrite !transportf_const in p ;
           exact p).
  Defined.

  Definition z_iso_weq_twosided_disp_cat_iso
             (x : C₁)
             (y : C₂)
             (z₁ z₂ : D)
    : z_iso z₁ z₂
      ≃
      @iso_twosided_disp
        _ _
        constant_twosided_disp_cat
        _ _ _ _
        (identity_z_iso x) (identity_z_iso y)
        z₁ z₂.
  Proof.
    use make_weq.
    - exact (z_iso_to_twosided_disp_cat_iso x y).
    - use isweq_iso.
      + exact (twosided_disp_cat_iso_to_z_iso x y).
      + abstract
          (intro f ;
           use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ; cbn ;
           apply idpath).
      + abstract
          (intro f ;
           use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ; cbn ;
           apply idpath).
  Defined.

  (**
   3. Univalence
   *)
  Definition is_univalent_constant_twosided_disp_cat
             (HD : is_univalent D)
    : is_univalent_twosided_disp_cat constant_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ z₁ z₂.
    induction p₁, p₂.
    use weqhomot.
    - exact (z_iso_weq_twosided_disp_cat_iso x₁ y₁ z₁ z₂
             ∘ make_weq _ (HD z₁ z₂))%weq.
    - abstract
        (intro p ;
         cbn in p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ; cbn ;
         apply idpath).
  Defined.
End ConstantTwoSidedDispCat.
