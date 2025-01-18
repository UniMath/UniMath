(**********************************************************************************************

 2-sided displayed categories over displayed categories

 Suppose that we have a 2-sided displayed category `D₁₂` over categories `C₁` and `C₂`. Then
 we are able to lift `D₁₂` to total categories of displayed categories. More specifically, if
 we also have displayed categories `D₁` over C₁` and `D₂` over `C₂`, then we can lift `D₁₂` to
 a 2-sided displayed category over the total categories over `D₁` and `D₂`. The displayed
 objects and morphisms are the same as in `D₁₂`. Intuitively, this construction means that we
 are able to add structure/properties to `C₁` and `C₂` and lift our 2-sided displayed category
 along that.

 Contents
 1. The 2-sided displayed category
 2. Isomorphisms in this 2-sided displayed category
 3. Properties of this 2-sided displayed category

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

Section TwoSidedDispCatAndDispCat.
  Context {C₁ C₂ : category}
          (D₁ : disp_cat C₁)
          (D₂ : disp_cat C₂)
          (D₁₂ : twosided_disp_cat C₁ C₂).

  Let E₁ : category := total_category D₁.
  Let E₂ : category := total_category D₂.

  (** * 1. The 2-sided displayed category *)
  Definition twosided_disp_cat_on_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor E₁ E₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D₁₂ (pr1 x) (pr1 y)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g, xy₁ -->[ pr1 f ][ pr1 g ] xy₂).
  Defined.

  Definition twosided_disp_cat_on_disp_cat_id_comp
    : twosided_disp_cat_id_comp twosided_disp_cat_on_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, id_two_disp xy).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂, fg₁ ;;2 fg₂).
  Defined.

  Definition twosided_disp_cat_on_disp_cat_data
    : twosided_disp_cat_data E₁ E₂.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_on_disp_cat_ob_mor.
    - exact twosided_disp_cat_on_disp_cat_id_comp.
  Defined.

  Proposition transportf_disp_mor2_twosided_disp_cat_on_disp_cat
              {x₁ x₂ : E₁}
              {f f' : x₁ --> x₂}
              (p : f = f')
              {y₁ y₂ : E₂}
              {g g' : y₁ --> y₂}
              (q : g = g')
              {xy₁ : twosided_disp_cat_on_disp_cat_data x₁ y₁}
              {xy₂ : twosided_disp_cat_on_disp_cat_data x₂ y₂}
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportf_disp_mor2 p q fg
      =
      transportf_disp_mor2 (maponpaths pr1 p) (maponpaths pr1 q) fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_twosided_disp_cat_on_disp_cat
              {x₁ x₂ : E₁}
              {f f' : x₁ --> x₂}
              (p : f' = f)
              {y₁ y₂ : E₂}
              {g g' : y₁ --> y₂}
              (q : g' = g)
              {xy₁ : twosided_disp_cat_on_disp_cat_data x₁ y₁}
              {xy₂ : twosided_disp_cat_on_disp_cat_data x₂ y₂}
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportb_disp_mor2 p q fg
      =
      transportb_disp_mor2 (maponpaths pr1 p) (maponpaths pr1 q) fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition twosided_disp_cat_on_disp_cat_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_on_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
      refine (id_two_disp_left _ @ _).
      use transportb_disp_mor2_eq.
      apply idpath.
    - intro ; intros.
      rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
      refine (id_two_disp_right _ @ _).
      use transportb_disp_mor2_eq.
      apply idpath.
    - intro ; intros.
      rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
      refine (assoc_two_disp _ _ _ @ _).
      use transportb_disp_mor2_eq.
      apply idpath.
    - intro ; intros.
      apply isaset_disp_mor.
  Qed.

  Definition twosided_disp_cat_on_disp_cat
    : twosided_disp_cat E₁ E₂.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_on_disp_cat_data.
    - exact twosided_disp_cat_on_disp_cat_axioms.
  Defined.

  (** * 2. Isomorphisms in this 2-sided displayed category *)
  Definition to_is_iso_twosided_disp_cat_on_disp_cat
             {x₁ x₂ : E₁}
             {f : x₁ --> x₂}
             (Hf : is_z_isomorphism f)
             {y₁ y₂ : E₂}
             {g : y₁ --> y₂}
             (Hg : is_z_isomorphism g)
             {xy₁ : twosided_disp_cat_on_disp_cat x₁ y₁}
             {xy₂ : twosided_disp_cat_on_disp_cat x₂ y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (is_z_iso_base_from_total Hf)
                      (is_z_iso_base_from_total Hg)
                      fg)
    : is_iso_twosided_disp Hf Hg fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         refine (inv_after_iso_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         refine (iso_after_inv_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition from_is_iso_twosided_disp_cat_on_disp_cat
             {x₁ x₂ : E₁}
             {f : x₁ --> x₂}
             (Hf : is_z_isomorphism f)
             {y₁ y₂ : E₂}
             {g : y₁ --> y₂}
             (Hg : is_z_isomorphism g)
             {xy₁ : twosided_disp_cat_on_disp_cat x₁ y₁}
             {xy₂ : twosided_disp_cat_on_disp_cat x₂ y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
             (Hfg : is_iso_twosided_disp Hf Hg fg)
    : is_iso_twosided_disp
        (is_z_iso_base_from_total Hf)
        (is_z_iso_base_from_total Hg)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition to_is_iso_twosided_disp_cat_on_disp_cat_id
             {x : E₁}
             {y : E₂}
             {xy₁ xy₂ : twosided_disp_cat_on_disp_cat x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (identity_is_z_iso (pr1 x))
                      (identity_is_z_iso (pr1 y))
                      fg)
    : is_iso_twosided_disp
        (identity_is_z_iso x)
        (identity_is_z_iso y)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition from_is_iso_twosided_disp_cat_on_disp_cat_id
             {x : E₁}
             {y : E₂}
             {xy₁ xy₂ : twosided_disp_cat_on_disp_cat x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (identity_is_z_iso x)
                      (identity_is_z_iso y)
                      fg)
    : is_iso_twosided_disp
        (identity_is_z_iso (pr1 x))
        (identity_is_z_iso (pr1 y))
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat ;
         cbn ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition to_iso_twosided_disp_cat_on_disp_cat
             {x : E₁}
             {y : E₂}
             {xy₁ xy₂ : twosided_disp_cat_on_disp_cat x y}
             (fg : iso_twosided_disp
                     (identity_z_iso (pr1 x)) (identity_z_iso (pr1 y))
                     xy₁ xy₂)
    : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) xy₁ xy₂.
  Proof.
    simple refine (_ ,, _).
    - exact fg.
    - use to_is_iso_twosided_disp_cat_on_disp_cat_id.
      apply fg.
  Defined.

  Definition from_iso_twosided_disp_cat_on_disp_cat
             {x : E₁}
             {y : E₂}
             {xy₁ xy₂ : twosided_disp_cat_on_disp_cat x y}
             (fg : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) xy₁ xy₂)
    : iso_twosided_disp
        (identity_z_iso (pr1 x)) (identity_z_iso (pr1 y))
        xy₁ xy₂.
  Proof.
    simple refine (_ ,, _).
    - exact fg.
    - use from_is_iso_twosided_disp_cat_on_disp_cat_id.
      apply fg.
  Defined.

  Definition iso_twosided_disp_cat_on_disp_cat_weq
             {x : E₁}
             {y : E₂}
             (xy₁ xy₂ : twosided_disp_cat_on_disp_cat x y)
    : iso_twosided_disp
        (identity_z_iso (pr1 x)) (identity_z_iso (pr1 y))
        xy₁ xy₂
      ≃
      iso_twosided_disp (identity_z_iso x) (identity_z_iso y) xy₁ xy₂.
  Proof.
    use weq_iso.
    - apply to_iso_twosided_disp_cat_on_disp_cat.
    - apply from_iso_twosided_disp_cat_on_disp_cat.
    - abstract
        (intro fg ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
    - abstract
        (intro fg ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  (** * 3. Properties of this 2-sided displayed category *)
  Definition is_univalent_twosided_disp_cat_on_disp_cat
             (H : is_univalent_twosided_disp_cat D₁₂)
    : is_univalent_twosided_disp_cat twosided_disp_cat_on_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p q xy₁ xy₂.
    induction p, q ; cbn.
    use weqhomot.
    - exact (iso_twosided_disp_cat_on_disp_cat_weq xy₁ xy₂
             ∘ make_weq _ (H _ _ _ _ (idpath _) (idpath _) xy₁ xy₂))%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      cbn.
      apply idpath.
  Qed.

  Proposition isaprop_mor_twosided_disp_cat_on_disp_cat
              (H : isaprop_disp_twosided_mor D₁₂)
    : isaprop_disp_twosided_mor twosided_disp_cat_on_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg fg'.
    apply H.
  Qed.

  Proposition all_disp_mor_iso_twosided_disp_cat_on_disp_cat
              (H : all_disp_mor_iso D₁₂)
    : all_disp_mor_iso twosided_disp_cat_on_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g Hf Hg fg.
    use to_is_iso_twosided_disp_cat_on_disp_cat.
    apply H.
  Defined.

  Proposition is_discrete_twosided_disp_cat_on_disp_cat
              (H : discrete_twosided_disp_cat D₁₂)
    : discrete_twosided_disp_cat twosided_disp_cat_on_disp_cat.
  Proof.
    simple refine (_ ,, _ ,, _).
    - use isaprop_mor_twosided_disp_cat_on_disp_cat.
      apply H.
    - use all_disp_mor_iso_twosided_disp_cat_on_disp_cat.
      apply H.
    - use is_univalent_twosided_disp_cat_on_disp_cat.
      apply H.
  Qed.
End TwoSidedDispCatAndDispCat.
