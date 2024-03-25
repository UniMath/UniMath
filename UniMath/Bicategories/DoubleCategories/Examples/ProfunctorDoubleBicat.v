(*****************************************************************************************

 The Verity double bicategory of profunctors

 In this file, we define the following Verity double bicategory:
 - Objects: univalent categories
 - Horizontal morphisms: functors
 - Horizontal 2-cells: natural transformations
 - Vertical morphisms: profunctors
 - Vertical 2-cells: natural transformations between profunctors
 - Squares: suitably typed natural transformations
 There are several interesting things to notice about this Verity double bicategory.

 First of all, we need to use Verity double bicategories instead of pseudo double
 categories. To get a pseudo double category of profunctors, one needs to use strict
 categories: this is to guarantee that we have a set of functors. However, the type of
 functors between two univalent categories does not form a set, and for that reason, we
 cannot have a pseudo double category.

 Second of all, the underlying horizontal bicategory is `Cat^co` rather than `Cat`. We
 need to reverse the 2-cells to guarantee that the natural transformations are correctly
 typed for the whiskering operations. Compare this to the Verity double bicategory of
 squares where we also had to reverse some 2-cells.

 Third of all, in this Verity double bicategory, the 2-cells coincide with certain squares.
 This is due to the fact they are defined to be natural transformations, just like both the
 horizontal and the vertical 2-cells.

 The data of this bicategory is given in other files. This file collects all of this data
 and puts it together in the shape of a Verity double bicategory. In addition, several
 laws are proven. All of those proofs boil down to technical stuff related to coends.

 Contents
 1. The 2-sided displayed category of the Verity bicategory of profunctors
 2. The vertical bicategory of profunctors
 3. The whiskering operations
 4. More laws
 5. The Verity double bicategory of univalent categories and profunctors
 6. 2-cells versus squares
 7. Companion pairs and conjoints of profunctors
 8. Vertical invertible 2-cells of profunctors
 9. The local univalence of the Verity double bicategory of squares
 10. The global univalence of the Verity double bicategory of squares

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.HSET.SetCoends.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Squares.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ProfunctorTwosidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.Core.

Local Open Scope cat.
Local Open Scope double_bicat.

Local Notation "∁" := (op2_bicat bicat_of_univ_cats).

(** * 1. The 2-sided displayed category of the Verity bicategory of profunctors *)
Definition univcat_profunctor_twosided_disp_cat_ob_mor
  : twosided_disp_cat_ob_mor ∁ ∁.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C₁ C₂ : univalent_category), C₁ ↛ C₂).
  - exact (λ (C₁ C₂ D₁ D₂ : univalent_category)
             (P : C₁ ↛ D₁)
             (Q : C₂ ↛ D₂)
             (F : C₁ ⟶ C₂)
             (G : D₁ ⟶ D₂),
           profunctor_square G F P Q).
Defined.

Proposition univcat_profunctor_twosided_disp_cat_id_comp
  : twosided_disp_cat_id_comp univcat_profunctor_twosided_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ C D P, id_h_profunctor_square P).
  - exact (λ C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ F₁ F₂ G₁ G₂ τ₁ τ₂, comp_h_profunctor_square τ₁ τ₂).
Defined.

Definition univcat_profunctor_twosided_disp_cat_data
  : twosided_disp_cat_data ∁ ∁.
Proof.
  simple refine (_ ,, _).
  - exact univcat_profunctor_twosided_disp_cat_ob_mor.
  - exact univcat_profunctor_twosided_disp_cat_id_comp.
Defined.

Definition univcat_profunctor_ver_sq_bicat
  : ver_sq_bicat.
Proof.
  use make_ver_sq_bicat.
  - exact ∁.
  - exact univcat_profunctor_twosided_disp_cat_data.
Defined.

(** * 2. The vertical bicategory of profunctors *)
Definition univcat_profunctor_ver_sq_bicat_ver_id_comp
  : ver_sq_bicat_ver_id_comp univcat_profunctor_ver_sq_bicat.
Proof.
  split.
  - split.
    + exact (λ (C : univalent_category), id_profunctor C).
    + exact (λ (C₁ C₂ C₃ : univalent_category)
               (P : C₁ ↛ C₂)
               (Q : C₂ ↛ C₃),
             comp_profunctor P Q).
  - exact (λ (C₁ C₂ : univalent_category) (P Q : C₁ ↛ C₂), profunctor_nat_trans P Q).
Defined.

Definition univcat_profunctor_ver_sq_bicat_id_comp_cells
  : ver_sq_bicat_id_comp_cells univcat_profunctor_ver_sq_bicat_ver_id_comp.
Proof.
  repeat split.
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           profunctor_nat_trans_id P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           lunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           runitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           linvunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           rinvunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (P : C₁ ↛ C₂)
             (Q : C₂ ↛ C₃)
             (R : C₃ ↛ C₄),
           inv_associator_profunctor_nat_trans P Q R).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (P : C₁ ↛ C₂)
             (Q : C₂ ↛ C₃)
             (R : C₃ ↛ C₄),
           associator_profunctor_nat_trans P Q R).
  - exact (λ (C₁ C₂ : univalent_category)
             (P Q R : C₁ ↛ C₂)
             (τ : profunctor_nat_trans P Q)
             (θ : profunctor_nat_trans Q R),
           profunctor_nat_trans_comp τ θ).
  - exact (λ (C₁ C₂ C₃ : univalent_category)
             (P : C₁ ↛ C₂)
             (Q₁ Q₂ : C₂ ↛ C₃)
             (τ : profunctor_nat_trans Q₁ Q₂),
           lwhisker_profunctor_nat_trans P τ).
  - exact (λ (C₁ C₂ C₃ : univalent_category)
             (P₁ P₂ : C₁ ↛ C₂)
             (Q : C₂ ↛ C₃)
             (τ : profunctor_nat_trans P₁ P₂),
           rwhisker_profunctor_nat_trans τ Q).
Defined.

Proposition univcat_profunctor_ver_sq_bicat_prebicat_laws
  : ver_sq_bicat_prebicat_laws univcat_profunctor_ver_sq_bicat_id_comp_cells.
Proof.
  repeat split.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    exact (lwhisker_profunctor_nat_trans_mor_comm P (profunctor_nat_trans_id Q) h h').
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    exact (rwhisker_profunctor_nat_trans_mor_comm (profunctor_nat_trans_id P) Q h h').
  - intros C₁ C₂ C₃ P Q₁ Q₂ Q₃ τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    etrans.
    {
      apply maponpaths.
      exact (lwhisker_profunctor_nat_trans_mor_comm P τ₁ h h').
    }
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm P τ₂ h (τ₁ z y h')).
    }
    refine (!_).
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm
               P (profunctor_nat_trans_comp τ₁ τ₂)
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P₁ P₂ P₃ Q τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    etrans.
    {
      apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm τ₁ Q h h').
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm τ₂ Q (τ₁ y x h) h').
    }
    refine (!_).
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm
               (profunctor_nat_trans_comp τ₁ τ₂) Q
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros w h h' ; cbn in *.
    etrans.
    {
      apply maponpaths.
      exact (lwhisker_profunctor_nat_trans_mor_comm (id_profunctor C₁) τ h h').
    }
    rewrite !lunitor_profunctor_nat_trans_mor_comm.
    rewrite <- profunctor_nat_trans_rmap.
    apply idpath.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros w h h' ; cbn in *.
    etrans.
    {
      apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm τ (id_profunctor C₂) h h').
    }
    rewrite !runitor_profunctor_nat_trans_mor_comm.
    rewrite <- profunctor_nat_trans_lmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ P Q R₁ R₂ τ.
    use eq_profunctor_nat_trans.
    intros z w h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros x h h' ; cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           Q R₁
           z x
           (λ h',
            associator_profunctor_nat_trans_mor
              P Q R₂ z w
              (lwhisker_profunctor_nat_trans_mor
                 P (lwhisker_profunctor_nat_trans Q τ) z w
                 (comp_profunctor_ob_in P (comp_profunctor Q R₁) x h h')))
           (λ h',
            lwhisker_profunctor_nat_trans_mor
              (comp_profunctor P Q) τ z w
              (associator_profunctor_nat_trans_mor
                 P Q R₁ z w
                 (comp_profunctor_ob_in P (comp_profunctor Q R₁) x h h')))).
    clear h'.
    intros y h' h'' ; cbn.
    etrans.
    {
      apply maponpaths.
      apply lwhisker_profunctor_nat_trans_mor_comm.
    }
    cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply lwhisker_profunctor_nat_trans_mor_comm.
    }
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm P Q R₂ h h' (τ z y h'')).
    }
    refine (!_).
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm P Q R₁ h h' h'').
    }
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm
               (comp_profunctor P Q) τ
               (comp_profunctor_ob_in P Q x h h') h'').
    }
    apply idpath.
  - intros C₁ C₂ C₃ C₄ P Q₁ Q₂ R τ.
    use eq_profunctor_nat_trans.
    intros z w h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros x h h' ; cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           Q₁ R
           z x
           (λ h',
            associator_profunctor_nat_trans_mor
              P Q₂ R z w
              (lwhisker_profunctor_nat_trans_mor
                 P (rwhisker_profunctor_nat_trans τ R)
                 z w
                 (comp_profunctor_ob_in P (comp_profunctor Q₁ R) x h h')))
           (λ h',
            rwhisker_profunctor_nat_trans_mor
              (lwhisker_profunctor_nat_trans P τ) R z w
              (associator_profunctor_nat_trans_mor
                 P Q₁ R z w
                 (comp_profunctor_ob_in P (comp_profunctor Q₁ R) x h h')))).
    clear h'.
    intros y h' h'' ; cbn.
    etrans.
    {
      apply maponpaths.
      apply lwhisker_profunctor_nat_trans_mor_comm.
    }
    cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply rwhisker_profunctor_nat_trans_mor_comm.
    }
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm P Q₂ R h (τ y x h') h'').
    }
    refine (!_).
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm P Q₁ R h h' h'').
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm
               (lwhisker_profunctor_nat_trans P τ) R
               (comp_profunctor_ob_in P Q₁ x h h') h'').
    }
    etrans.
    {
      apply maponpaths_2.
      exact (lwhisker_profunctor_nat_trans_mor_comm P τ h h').
    }
    apply idpath.
  - intros C₁ C₂ C₃ C₄ P₁ P₂ Q R τ.
    use eq_profunctor_nat_trans.
    intros z w h.
    use mor_from_comp_profunctor_ob_eq.
    clear h ; cbn.
    intros x h h'.
    use (mor_from_comp_profunctor_ob_eq
           Q R z x
           (λ h',
            rwhisker_profunctor_nat_trans_mor
              (rwhisker_profunctor_nat_trans τ Q) R z w
              (associator_profunctor_nat_trans_mor
                 P₁ Q R z w
                 (comp_profunctor_ob_in P₁ (comp_profunctor Q R) x h h')))
           (λ h',
            associator_profunctor_nat_trans_mor
              P₂ Q R z w
              (rwhisker_profunctor_nat_trans_mor
                 τ (comp_profunctor Q R) z w
                 (comp_profunctor_ob_in P₁ (comp_profunctor Q R) x h h')))).
    clear h'.
    intros y h' h'' ; cbn in *.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm P₁ Q R h h' h'').
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm
               (rwhisker_profunctor_nat_trans τ Q) R
               (comp_profunctor_ob_in P₁ Q x h h') h'').
    }
    cbn.
    etrans.
    {
      apply maponpaths_2.
      exact (rwhisker_profunctor_nat_trans_mor_comm τ Q h h').
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm
               τ (comp_profunctor Q R)
               h (comp_profunctor_ob_in Q R y h' h'')).
    }
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm P₂ Q R (τ x w h) h' h'').
    }
    apply idpath.
  - intros C₁ C₂ C₃ P₁ P₂ Q₁ Q₂ τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    etrans.
    {
      apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm τ₁ Q₁ h h').
    }
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm P₂ τ₂ (τ₁ y x h) h').
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (lwhisker_profunctor_nat_trans_mor_comm P₁ τ₂ h h').
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm τ₁ Q₂ h (τ₂ z y h')).
    }
    apply idpath.
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_runitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_runitor_profunctor_nat_trans P)).
  - intros C₁ C₂ C₃ C₄ P Q R.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_associator_profunctor_nat_trans P Q R)).
  - intros C₁ C₂ C₃ C₄ P Q R.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_associator_profunctor_nat_trans P Q R)).
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           (id_profunctor C₂) Q
           z y
           (λ h',
            rwhisker_profunctor_nat_trans_mor
              (runitor_profunctor_nat_trans P) Q z x
              (associator_profunctor_nat_trans_mor
                 P (id_profunctor C₂) Q z x
                 (comp_profunctor_ob_in
                    P (comp_profunctor (id_profunctor C₂) Q)
                    y h h')))
           (λ h',
            lwhisker_profunctor_nat_trans_mor
              P (lunitor_profunctor_nat_trans Q) z x
              (comp_profunctor_ob_in
                 P (comp_profunctor (id_profunctor C₂) Q) y h h'))).
    clear h'.
    intros y' h' h'' ; cbn in *.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm
               P (id_profunctor C₂) Q
               h h' h'').
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm
               (runitor_profunctor_nat_trans P) Q
               (comp_profunctor_ob_in P (id_profunctor C₂) y h h') h'').
    }
    cbn.
    rewrite runitor_profunctor_nat_trans_mor_comm.
    refine (!_).
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm
               P (lunitor_profunctor_nat_trans Q)
               h (comp_profunctor_ob_in (id_profunctor C₂) Q y' h' h'')).
    }
    cbn.
    rewrite lunitor_profunctor_nat_trans_mor_comm.
    rewrite comp_profunctor_ob_in_comm.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ P₁ P₂ P₃ P₄.
    use eq_profunctor_nat_trans.
    intros z v h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros w h k ; cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           P₂ (comp_profunctor P₃ P₄)
           z w
           (λ k,
            rwhisker_profunctor_nat_trans_mor
              (associator_profunctor_nat_trans P₁ P₂ P₃) P₄ z v
              (associator_profunctor_nat_trans_mor
                 P₁ (comp_profunctor P₂ P₃) P₄ z v
                 (lwhisker_profunctor_nat_trans_mor
                    P₁ (associator_profunctor_nat_trans P₂ P₃ P₄) z v
                    (comp_profunctor_ob_in
                       P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                       w h k))))
           (λ k,
            associator_profunctor_nat_trans_mor
              (comp_profunctor P₁ P₂) P₃ P₄ z v
              (associator_profunctor_nat_trans_mor
                 P₁ P₂ (comp_profunctor P₃ P₄) z v
                 (comp_profunctor_ob_in
                    P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                    w h k)))).
    clear k.
    intros x k l ; cbn.
    use (mor_from_comp_profunctor_ob_eq
           P₃ P₄
           z x
           (λ l,
            rwhisker_profunctor_nat_trans_mor
              (associator_profunctor_nat_trans P₁ P₂ P₃) P₄ z v
              (associator_profunctor_nat_trans_mor
                 P₁ (comp_profunctor P₂ P₃) P₄ z v
                 (lwhisker_profunctor_nat_trans_mor
                    P₁ (associator_profunctor_nat_trans P₂ P₃ P₄) z v
                    (comp_profunctor_ob_in
                       P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄)) w h
                       (comp_profunctor_ob_in
                          P₂ (comp_profunctor P₃ P₄) x k l)))))
           (λ l,
            associator_profunctor_nat_trans_mor
              (comp_profunctor P₁ P₂) P₃ P₄ z v
              (associator_profunctor_nat_trans_mor
                 P₁ P₂ (comp_profunctor P₃ P₄) z v
                 (comp_profunctor_ob_in
                    P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄)) w h
                    (comp_profunctor_ob_in
                       P₂ (comp_profunctor P₃ P₄) x k l))))).
    clear l.
    intros y l m ; cbn.
    etrans.
    {
      do 2 apply maponpaths.
      exact (lwhisker_profunctor_nat_trans_mor_comm
               P₁ (associator_profunctor_nat_trans P₂ P₃ P₄)
               h
               (comp_profunctor_ob_in
                  P₂ (comp_profunctor P₃ P₄) x k
                  (comp_profunctor_ob_in P₃ P₄ y l m))).
    }
    cbn.
    rewrite !associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      do 2 apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm P₂ P₃ P₄ k l m).
    }
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm
               P₁ (comp_profunctor P₂ P₃) P₄
               h
               (comp_profunctor_ob_in P₂ P₃ x k l)
               m).
    }
    etrans.
    {
      exact (rwhisker_profunctor_nat_trans_mor_comm
               (associator_profunctor_nat_trans P₁ P₂ P₃) P₄
               _
               m).
    }
    cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths_2.
      exact (associator_profunctor_nat_trans_mor_ob_comm P₁ P₂ P₃ h k l).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (associator_profunctor_nat_trans_mor_ob_comm
               P₁ P₂ (comp_profunctor P₃ P₄)
               h k _).
    }
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm
               (comp_profunctor P₁ P₂) P₃ P₄
               _ l m).
    }
    apply idpath.
Qed.

Definition univcat_profunctor_ver_bicat_sq_bicat
  : ver_bicat_sq_bicat.
Proof.
  use make_ver_bicat_sq_bicat.
  - exact univcat_profunctor_ver_sq_bicat.
  - exact univcat_profunctor_ver_sq_bicat_ver_id_comp.
  - exact univcat_profunctor_ver_sq_bicat_id_comp_cells.
  - exact univcat_profunctor_ver_sq_bicat_prebicat_laws.
  - abstract
      (intros C₁ C₂ P Q ;
       apply isaset_profunctor_nat_trans).
Defined.

Definition univcat_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq
  : ver_bicat_sq_bicat_ver_id_comp_sq univcat_profunctor_ver_bicat_sq_bicat.
Proof.
  split.
  - exact (λ (C₁ C₂ : univalent_category)
             (F : C₁ ⟶ C₂),
           id_v_profunctor_square F).
  - exact (λ (C₁ C₂ C₃ D₁ D₂ D₃ : univalent_category)
             (F₁ : C₁ ⟶ D₁)
             (F₂ : C₂ ⟶ D₂)
             (F₃ : C₃ ⟶ D₃)
             (P₁ : C₁ ↛ C₂)
             (P₂ : C₂ ↛ C₃)
             (Q₁ : D₁ ↛ D₂)
             (Q₂ : D₂ ↛ D₃)
             (τ : profunctor_square F₂ F₁ P₁ Q₁)
             (θ : profunctor_square F₃ F₂ P₂ Q₂),
           comp_v_profunctor_square τ θ).
Defined.

Definition univcat_profunctor_ver_bicat_sq_bicat_ver_id_comp
  : ver_bicat_sq_bicat_ver_id_comp.
Proof.
  use make_ver_bicat_sq_bicat_ver_id_comp.
  - exact univcat_profunctor_ver_bicat_sq_bicat.
  - exact univcat_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq.
Defined.

(** * 3. The whiskering operations *)
Definition univcat_profunctor_double_bicat_whiskering
  : double_bicat_whiskering univcat_profunctor_ver_bicat_sq_bicat_ver_id_comp.
Proof.
  repeat split.
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P₁ P₂ : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : profunctor_nat_trans P₁ P₂)
             (s : profunctor_square G F P₂ Q),
           lwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q₁ Q₂ : C₂ ↛ C₄)
             (τ : profunctor_nat_trans Q₁ Q₂)
             (s : profunctor_square G F P Q₁),
           rwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F₁ F₂ : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : F₂ ⟹ F₁)
             (s : profunctor_square G F₂ P Q),
           dwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G₁ G₂ : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : G₂ ⟹ G₁)
             (s : profunctor_square G₁ F P Q),
           uwhisker_profunctor_square τ s).
Defined.

Definition univcat_profunctor_ver_bicat_sq_id_comp_whisker
  : ver_bicat_sq_id_comp_whisker.
Proof.
  use make_ver_bicat_sq_id_comp_whisker.
  - exact univcat_profunctor_ver_bicat_sq_bicat_ver_id_comp.
  - exact univcat_profunctor_double_bicat_whiskering.
Defined.

(** * 4. More laws *)
Proposition univcat_profunctor_whisker_square_bicat_law
  : whisker_square_bicat_law univcat_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P₁ P₂ P₃ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q₁ Q₂ Q₃ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ G P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_comp.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite lmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ G₃ P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite lmap_comp.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G₁ G₂ P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_lmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G P₁ P₂ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G P Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite profunctor_nat_trans_rmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ P₁ P₂ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ P Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite profunctor_nat_trans_lmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P₁ P₂ Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite id_left, id_right.
    rewrite nat_trans_ax.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq ; clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm θ₁ θ₂ z x y h h').
    }
    rewrite comp_profunctor_mor_comm.
    rewrite lmap_id.
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (dwhisker_profunctor_square τ θ₁) θ₂
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F G H₁ H₂ P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm θ₁ θ₂ z x y h h').
    }
    rewrite comp_profunctor_mor_comm.
    rewrite rmap_id.
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ (uwhisker_profunctor_square τ θ₂)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F G₁ G₂ H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    use mor_from_comp_profunctor_ob_eq ; cbn.
    clear h.
    intros y h h'.
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ (dwhisker_profunctor_square τ θ₂)
               z x y
               h h').
    }
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (uwhisker_profunctor_square τ θ₁) θ₂
               z x y h h').
    }
    cbn.
    rewrite comp_profunctor_ob_in_comm.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P₁ P₂ Q R τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q₁ Q₂ R τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q R₁ R₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
Qed.

Proposition univcat_profunctor_double_bicat_id_comp_square_laws
  : double_bicat_id_comp_square_laws univcat_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₀ P₁ P₂ Q₁ Q₂ R₁ R₂ F₁ F₂ G₁ G₂ H₁ H₂ τ₁ τ₂ θ₁ θ₂.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h ; cbn in *.
    intros y h h'.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₁ τ₂ z x y h h').
    }
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ θ₂
               (H₁ z) (F₁ x) (G₁ y)
               (τ₁ y x h) (τ₂ z y h')).
    }
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (comp_h_profunctor_square τ₁ θ₁) (comp_h_profunctor_square τ₂ θ₂)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intro C.
    use eq_profunctor_square ; intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (id_h_profunctor_square P) (id_h_profunctor_square Q)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_square ; intros z x h ; cbn in *.
    apply idpath.
Qed.

Proposition univcat_profunctor_double_bicat_cylinder_laws
  : double_bicat_cylinder_laws univcat_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ F₁ F₂ F₃ G₁ G₂ G₃ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ F₁ F₂ F₃ F₄ P₁ P₂ P₃ Q₁ Q₂ Q₃ τ₁ τ₂ τ₃.
    use eq_profunctor_square.
    intros x₁ x₂ h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros x₃ h h'.
    cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           P₂ P₃
           x₁ x₃
           (λ h',
            comp_v_profunctor_square_mor
              (comp_v_profunctor_square τ₁ τ₂) τ₃
              x₁ x₂
              (associator_profunctor_nat_trans_mor
                 P₁ P₂ P₃ x₁ x₂
                 (comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x₃ h h')))
           (λ h',
            associator_profunctor_nat_trans_mor
              Q₁ Q₂ Q₃ (F₄ x₁) (F₁ x₂)
              (comp_v_profunctor_square_mor
                 τ₁ (comp_v_profunctor_square τ₂ τ₃) x₁ x₂
                 (comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x₃ h h')))).
    clear h'.
    intros x₄ h' h'' ; cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply associator_profunctor_nat_trans_mor_ob_comm.
    }
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (comp_v_profunctor_square τ₁ τ₂) τ₃
               _ _ _
               _ _).
    }
    cbn.
    etrans.
    {
      apply maponpaths_2.
      exact (comp_v_profunctor_square_mor_comm τ₁ τ₂ _ _ _ _ _).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₁ (comp_v_profunctor_square τ₂ τ₃) _ _ _ _ _).
    }
    rewrite associator_profunctor_nat_trans_mor_comm ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₂ τ₃ _ _ _ _ _).
    }
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm
               Q₁ Q₂ Q₃
               (τ₁ x₃ x₂ h)
               (τ₂ x₄ x₃ h')
               (τ₃ x₁ x₄ h'')).
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros z h h' ; cbn in *.
    rewrite lunitor_profunctor_nat_trans_mor_comm.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm (id_v_profunctor_square F) τ y x z h h').
    }
    cbn.
    rewrite lunitor_profunctor_nat_trans_mor_comm.
    rewrite (profunctor_square_rmap τ).
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros z h h' ; cbn in *.
    rewrite runitor_profunctor_nat_trans_mor_comm.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ (id_v_profunctor_square G) y x z h h').
    }
    cbn.
    rewrite runitor_profunctor_nat_trans_mor_comm.
    rewrite (profunctor_square_lmap τ).
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ F₃ P₁ P₂ P₁' P₂' Q₁ Q₂ Q₁' Q₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂'.
    intros p q.
    use eq_profunctor_square.
    intros x₁ x₂ h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros x₃ h h' ; cbn in *.
    etrans.
    {
      do 2 apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm τ₁ P₁' h h').
    }
    etrans.
    {
      apply maponpaths.
      exact (lwhisker_profunctor_nat_trans_mor_comm P₂ τ₂ (τ₁ x₃ x₂ h) h').
    }
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               s₁' s₂'
               x₁ x₂ x₃
               (τ₁ x₃ x₂ h) (τ₂ x₁ x₃ h')).
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm s₁ s₂ x₁ x₂ x₃ h h').
    }
    etrans.
    {
      apply maponpaths.
      exact (rwhisker_profunctor_nat_trans_mor_comm
               θ₁ Q₁'
               (s₁ x₃ x₂ h) (s₂ x₁ x₃ h')).
    }
    cbn.
    etrans.
    {
      exact (lwhisker_profunctor_nat_trans_mor_comm
               Q₂ θ₂
               (θ₁ (F₂ x₃) (F₁ x₂) (s₁ x₃ x₂ h)) (s₂ x₁ x₃ h')).
    }
    cbn.
    pose (profunctor_square_eq_pointwise p h) as p'.
    pose (profunctor_square_eq_pointwise q h') as q'.
    cbn in p', q'.
    rewrite q'.
    rewrite p'.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ F₃ P₁ P₂ P₁' P₂' Q₁ Q₂ Q₁' Q₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂'.
    intros p q.
    use eq_profunctor_square.
    intros x₁ x₂ h ; cbn in *.
    rewrite lmap_comp.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (profunctor_square_lmap s₂).
    }
    etrans.
    {
      apply (profunctor_square_eq_pointwise q).
    }
    cbn.
    etrans.
    {
      do 2 apply maponpaths.
      exact (profunctor_square_eq_pointwise p h).
    }
    cbn.
    rewrite (profunctor_square_rmap s₂').
    rewrite <- rmap_comp.
    apply maponpaths_2.
    rewrite nat_trans_ax.
    apply idpath.
Qed.

Proposition univcat_profunctor_double_bicat_laws
  : double_bicat_laws univcat_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  use make_double_bicat_laws.
  - exact univcat_profunctor_whisker_square_bicat_law.
  - exact univcat_profunctor_double_bicat_id_comp_square_laws.
  - exact univcat_profunctor_double_bicat_cylinder_laws.
  - intro ; intros.
    apply isaset_profunctor_square.
Qed.

(** * 5. The Verity double bicategory of univalent categories and profunctors *)
Definition univcat_profunctor_verity_double_bicat
  : verity_double_bicat.
Proof.
  use make_verity_double_bicat.
  - exact univcat_profunctor_ver_bicat_sq_id_comp_whisker.
  - exact univcat_profunctor_double_bicat_laws.
Defined.

(** * 6. 2-cells versus squares *)
Definition univcat_profunctor_vertically_saturated
  : vertically_saturated
      univcat_profunctor_verity_double_bicat.
Proof.
  intros C₁ C₂ P Q ; cbn in *.
  use isweq_iso.
  - exact profunctor_square_to_profunctor_nat_trans.
  - abstract
      (intros τ ;
       use eq_profunctor_nat_trans ;
       intros y x h ; cbn ;
       apply idpath).
  - abstract
      (intros τ ;
       use eq_profunctor_square ;
       intros y x h ; cbn ;
       apply idpath).
Defined.

Definition univcat_profunctor_horizontally_saturated
  : horizontally_saturated
      univcat_profunctor_verity_double_bicat.
Proof.
  intros C₁ C₂ F G ; cbn in *.
  use isweq_iso.
  - exact profunctor_square_to_nat_trans.
  - abstract
      (intro τ ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite functor_id ;
       rewrite !id_left ;
       apply idpath).
  - abstract
      (intros τ ;
       use eq_profunctor_square ;
       intros x y f ; cbn in * ;
       rewrite !id_left ;
       pose (profunctor_square_natural τ f (identity y) (identity y)) as p ;
       cbn in p ;
       rewrite functor_id in p ;
       rewrite !id_right in p ;
       exact (!p)).
Defined.

Definition univcat_profunctor_is_weak_double_cat
  : is_weak_double_cat univcat_profunctor_verity_double_bicat.
Proof.
  split.
  - exact univcat_profunctor_vertically_saturated.
  - exact univcat_profunctor_horizontally_saturated.
Defined.

(** * 7. Companion pairs of profunctors *)
Definition all_companions_univcat_profunctor_verity_double_bicat
  : all_companions univcat_profunctor_verity_double_bicat.
Proof.
  refine (λ (C₁ C₂ : univalent_category)
            (F : C₁ ⟶ C₂),
          representable_profunctor_left F ,, _).
  use make_are_companions ; cbn.
  - apply representable_profunctor_left_unit.
  - apply representable_profunctor_left_counit.
  - abstract
      (use eq_profunctor_square ;
       intros y x h ; cbn in * ;
       etrans ;
       [ apply maponpaths ;
         apply (comp_v_profunctor_square_mor_comm
                  (representable_profunctor_left_counit F)
                  (representable_profunctor_left_unit F))
       | ] ;
       rewrite runitor_profunctor_nat_trans_mor_comm ;
       cbn ;
       rewrite !functor_id ;
       rewrite !id_right ;
       apply idpath).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ; cbn in * ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.

Definition all_conjoints_univcat_profunctor_verity_double_bicat
  : all_conjoints univcat_profunctor_verity_double_bicat.
Proof.
  refine (λ (C₁ C₂ : univalent_category)
            (F : C₁ ⟶ C₂),
          representable_profunctor_right F ,, _).
  use make_are_conjoints ; cbn.
  - apply representable_profunctor_right_unit.
  - apply representable_profunctor_right_counit.
  - abstract
      (use eq_profunctor_square ;
       intros y x h ; cbn in * ;
       etrans ;
       [ apply maponpaths ;
         apply (comp_v_profunctor_square_mor_comm
                  (representable_profunctor_right_counit F)
                  (representable_profunctor_right_unit F))
       | ] ;
       rewrite lunitor_profunctor_nat_trans_mor_comm ;
       cbn ;
       rewrite !functor_id ;
       rewrite !id_left ;
       apply idpath).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ; cbn in * ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.

(** * 8. Vertical invertible 2-cells of profunctors *)
Definition profunctor_nat_iso_weq_vertible_invertible_2cell
           {C₁ C₂ : univcat_profunctor_verity_double_bicat}
           {P Q : C₁ -|-> C₂}
           (τ : P =|=> Q)
  : is_profunctor_nat_iso τ ≃ is_invertible_2cell τ.
Proof.
  use weqimplimpl.
  - intros Hτ.
    use make_is_invertible_2cell.
    + exact (inv_profunctor_nat_trans Hτ).
    + apply inv_profunctor_nat_trans_right.
    + apply inv_profunctor_nat_trans_left.
  - intros Hτ y x.
    use isweq_iso.
    + intros h.
      exact ((Hτ^-1 : profunctor_nat_trans _ _) y x h).
    + abstract
        (intros h ; cbn ;
         exact (profunctor_nat_trans_eq_pointwise (vcomp_rinv Hτ) h)).
    + abstract
        (intros h ; cbn ;
         exact (profunctor_nat_trans_eq_pointwise (vcomp_linv Hτ) h)).
  - apply isaprop_is_profunctor_nat_iso.
  - apply isaprop_is_invertible_2cell.
Defined.

(** * 9. The local univalence of the Verity double bicategory of squares *)
Definition ver_locally_univcat_profunctor_verity_double_bicat
  : ver_locally_univalent univcat_profunctor_verity_double_bicat.
Proof.
  intros C₁ C₂ P Q.
  use weqhomot.
  - exact (weqfibtototal _ _ profunctor_nat_iso_weq_vertible_invertible_2cell
           ∘ path_profunctor_weq_profunctor_nat_iso P Q)%weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    cbn.
    apply idpath.
Qed.

Definition locally_univcat_profunctor_verity_double_bicat
  : locally_univalent_verity_double_bicat univcat_profunctor_verity_double_bicat.
Proof.
  split.
  - use op2_bicat_is_univalent_2_1.
    exact univalent_cat_is_univalent_2_1.
  - exact ver_locally_univcat_profunctor_verity_double_bicat.
Defined.

(** * 10. The global univalence of the Verity double bicategory of squares *)
Definition hor_globally_univcat_profunctor_verity_double_bicat
  : hor_globally_univalent univcat_profunctor_verity_double_bicat.
Proof.
  use op2_bicat_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_0.
Defined.

Definition gregarious_univcat_profunctor_verity_double_bicat
  : gregarious_univalent univcat_profunctor_verity_double_bicat.
Proof.
  use hor_globally_univalent_to_gregarious_univalent.
  - exact locally_univcat_profunctor_verity_double_bicat.
  - exact hor_globally_univcat_profunctor_verity_double_bicat.
  - exact univcat_profunctor_vertically_saturated.
Defined.
