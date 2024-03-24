(**********************************************************************************

 The double category of lenses

 In this file, we define the double category of lenses. Suppose that `C` is a
 category with binary products. Then we define the following double category:
 - Objects: those of `C`
 - Vertical morphisms: morphisms in `C`
 - Horizontal morphisms: lenses in `C`
 The squares in this double category are commutative squares.

 This double category is essentially also constructed in Proposition 2.0.4 in
 "Categories of Optics" by Riley ( https://arxiv.org/pdf/1809.00738.pdf).
 There are two difference between the formalization in this file and the reference.
 In the reference, a category of lenses is constructed, and this amounts to
 constructing the horizontal composition and identities of lenses, whereas here
 a double category is constructed. The other difference is the method taken: the
 reference uses an abstract theorem about optics, whereas we construct the desired
 double category directly.

 Note that a double category of lenses has also been considered by Clarke in
 "The double category of lenses" (https://figshare.mq.edu.au/articles/thesis/The_double_category_of_lenses/22045073/1).
 The difference between the formalization and that thesis is that a different
 notion of lens is considered. Clarke looks at delta-lenses, so the resulting
 double category is as follows:
 - Objects: categories
 - Vertical morphisms: delta-lenses
 - Horizontal morphisms: functors
 This is different from what we look at, because we look at lenses in a category
 with finite products.

 We provide both a univalent and a strict version.

 Contents
 1. The horizontal identity
 2. Horizontal composition
 3. Unitors and associators
 4. The double category
 5. The strict double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Lenses.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.StrictDoubleCats.

Local Open Scope cat.

Section LensesDoubleCat.
  Context (C : category)
          (PC : BinProducts C).

  (** * 1. The horizontal identity *)
  Definition lenses_double_cat_hor_id_data
    : hor_id_data (twosided_disp_cat_of_lenses C PC).
  Proof.
    use make_hor_id_data.
    - exact (identity_lens _ _).
    - exact (λ x y f, identity_lens_mor _ _ f).
  Defined.

  Definition lenses_double_cat_hor_id
    : hor_id (twosided_disp_cat_of_lenses C PC).
  Proof.
    use make_hor_id.
    - exact lenses_double_cat_hor_id_data.
    - abstract
        (split ;
         intros ;
         apply discrete_lenses_twosided_disp_cat).
  Defined.

  (** * 2. Horizontal composition *)
  Definition lenses_double_cat_hor_comp_data
    : hor_comp_data (twosided_disp_cat_of_lenses C PC).
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z l₁ l₂, comp_lens _ _ l₁ l₂).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ, comp_lens_mor _ _ φ ψ).
  Defined.

  Definition lenses_double_cat_hor_comp
    : hor_comp (twosided_disp_cat_of_lenses C PC).
  Proof.
    use make_hor_comp.
    - exact lenses_double_cat_hor_comp_data.
    - abstract
        (split ;
         intros ;
         apply discrete_lenses_twosided_disp_cat).
  Defined.

  (** * 3. Unitors and associators *)
  Definition lenses_double_cat_lunitor
    : double_cat_lunitor lenses_double_cat_hor_id lenses_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - intros x y f.
      use make_iso_twosided_disp.
      + use make_lens_mor ; cbn.
        * rewrite !id_left, !id_right.
          apply idpath.
        * rewrite id_right.
          rewrite !assoc'.
          rewrite BinProductOfArrowsPr1.
          rewrite !assoc.
          rewrite BinProductPr1Commutes.
          rewrite id_left.
          apply idpath.
      + apply discrete_lenses_twosided_disp_cat.
    - intro ; intros.
      apply discrete_lenses_twosided_disp_cat.
  Qed.

  Definition lenses_double_cat_runitor
    : double_cat_runitor lenses_double_cat_hor_id lenses_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - intros x y f.
      use make_iso_twosided_disp.
      + use make_lens_mor ; cbn.
        * rewrite !id_left, !id_right.
          apply idpath.
        * rewrite id_right.
          rewrite !assoc'.
          rewrite BinProductOfArrows_id.
          rewrite !assoc.
          apply maponpaths_2.
          refine (_ @ !(BinProductArrowEta _ _ _ _ _ _)).
          rewrite postcompWithBinProductArrow.
          rewrite !id_left, !id_right.
          rewrite BinProductOfArrowsPr1.
          rewrite id_right.
          apply idpath.
      + apply discrete_lenses_twosided_disp_cat.
    - intro ; intros.
      apply discrete_lenses_twosided_disp_cat.
  Qed.

  Definition lenses_double_cat_associator
    : double_cat_associator lenses_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - intros w x y z f g h.
     use make_iso_twosided_disp.
      + use make_lens_mor ; cbn.
        * rewrite !id_left, !id_right.
          rewrite !assoc.
          apply idpath.
        * rewrite id_right.
          rewrite !assoc'.
          rewrite BinProductOfArrows_id.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite id_left.
          rewrite !postcompWithBinProductArrow.
          rewrite !precompWithBinProductArrow.
          rewrite id_right.
          rewrite !postcompWithBinProductArrow.
          rewrite !id_left, !id_right.
          rewrite BinProductOfArrowsPr2.
          rewrite BinProductPr2Commutes.
          apply maponpaths_2.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite !postcompWithBinProductArrow.
          apply maponpaths_2.
          rewrite id_right.
          apply maponpaths_2.
          rewrite BinProductOfArrows_comp.
          rewrite id_right.
          apply idpath.
      + apply discrete_lenses_twosided_disp_cat.
    - intro ; intros.
      apply discrete_lenses_twosided_disp_cat.
  Qed.
End LensesDoubleCat.

(** * 4. The double category *)
Definition lenses_double_cat
           (C : category)
           (PC : BinProducts C)
  : double_cat.
Proof.
  use make_double_cat.
  - exact C.
  - exact (twosided_disp_cat_of_lenses C PC).
  - exact (lenses_double_cat_hor_id C PC).
  - exact (lenses_double_cat_hor_comp C PC).
  - exact (lenses_double_cat_lunitor C PC).
  - exact (lenses_double_cat_runitor C PC).
  - exact (lenses_double_cat_associator C PC).
  - abstract
      (intro ; intros ;
       apply discrete_lenses_twosided_disp_cat).
  - abstract
      (intro ; intros ;
       apply discrete_lenses_twosided_disp_cat).
Defined.

Definition lenses_double_cat_ver_weq_square
           (C : category)
           (PC : BinProducts C)
  : ver_weq_square (lenses_double_cat C PC).
Proof.
  intros x y f g.
  use isweqimplimpl.
  - intros p.
    pose (q := pr11 p) ; cbn in q.
    rewrite id_left, id_right in q.
    exact (!q).
  - apply homset_property.
  - use invproofirrelevance.
    intro ; intros.
    apply discrete_lenses_twosided_disp_cat.
Qed.

Definition lenses_univalent_double_cat
           (C : univalent_category)
           (PC : BinProducts C)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (lenses_double_cat C PC).
  - split.
    + apply univalent_category_is_univalent.
    + apply is_univalent_lenses_twosided_disp_cat.
Defined.

(** * 5. The strict double category *)
Definition lenses_strict_double_cat
           (C : setcategory)
           (PC : BinProducts C)
  : strict_double_cat.
Proof.
  use make_strict_double_cat.
  - exact C.
  - exact (twosided_disp_cat_of_lenses C PC).
  - apply is_strict_twosided_disp_cat_of_lenses.
  - exact (lenses_double_cat_hor_id C PC).
  - exact (lenses_double_cat_hor_comp C PC).
  - abstract
      (intros x y f ; cbn ;
       exact (lens_id_left C PC f)).
  - abstract
      (intros x y f ; cbn ;
       exact (lens_id_right C PC f)).
  - abstract
      (intros w x y z f g h ; cbn ;
       exact (lens_assoc C PC f g h)).
  - abstract
      (intro ; intros ;
       apply discrete_lenses_twosided_disp_cat).
  - abstract
      (intro ; intros ;
       apply discrete_lenses_twosided_disp_cat).
  - abstract
      (intro ; intros ;
       apply discrete_lenses_twosided_disp_cat).
Defined.
