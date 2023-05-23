#[local] Unset Universe Checking.
(**********************************************************************************

 The two-sided displayed category of lenses

 Reference for lenses:
   https://ncatlab.org/nlab/show/lens+%28in+computer+science%29

 We define the two-sided displayed category of lenses.

 Contents
 1. Definition via two-sided displayed categories
 2. Discreteness and univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.FiberwiseProduct.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section Lenses.
  Context (C : category)
          (prodC : BinProducts C).

  (**
   1. Definition via two-sided displayed categories
   *)
  Definition twosided_disp_cat_of_lenses_get_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ s v, s --> v).
    - exact (λ s₁ s₂ v₁ v₂ g₁ g₂ f₁ f₂, g₁ · f₂ = f₁ · g₂).
  Defined.

  Definition twosided_disp_cat_of_lenses_get_id_comp
    : twosided_disp_cat_id_comp
        twosided_disp_cat_of_lenses_get_ob_mor.
  Proof.
    split.
    - intros s v g ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros s₁ s₂ s₃ v₁ v₂ v₃ g₁ g₂ g₃ f₁ f₂ h₁ h₂ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition twosided_disp_cat_of_lenses_get_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_get_ob_mor.
    - exact twosided_disp_cat_of_lenses_get_id_comp.
  Defined.

  Definition twosided_disp_cat_of_lenses_get_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_of_lenses_get_data.
  Proof.
    repeat split ; intro ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition twosided_disp_cat_of_lenses_get
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_get_data.
    - exact twosided_disp_cat_of_lenses_get_axioms.
  Defined.

  Definition twosided_disp_cat_of_lenses_put_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ s v, BinProductObject _ (prodC v s) --> s).
    - exact (λ s₁ s₂ v₁ v₂ g₁ g₂ f₁ f₂,
             g₁ · f₁
             =
             BinProductOfArrows _ _ _ f₂ f₁ · g₂).
  Defined.

  Definition twosided_disp_cat_of_lenses_put_id_comp
    : twosided_disp_cat_id_comp
        twosided_disp_cat_of_lenses_put_ob_mor.
  Proof.
    split.
    - intros s v g ; cbn.
      rewrite id_right.
      assert (BinProductOfArrows C (prodC v s) (prodC v s) (identity v) (identity s)
              =
              identity _)
        as p.
      {
        refine (!_).
        use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
      }
      rewrite p.
      rewrite id_left.
      apply idpath.
    - intros s₁ s₂ s₃ v₁ v₂ v₃ g₁ g₂ g₃ f₁ f₂ h₁ h₂ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      rewrite !assoc.
      rewrite BinProductOfArrows_comp.
      apply idpath.
  Qed.

  Definition twosided_disp_cat_of_lenses_put_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_put_ob_mor.
    - exact twosided_disp_cat_of_lenses_put_id_comp.
  Defined.

  Definition twosided_disp_cat_of_lenses_put_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_of_lenses_put_data.
  Proof.
    repeat split ; intro ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition twosided_disp_cat_of_lenses_put
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_put_data.
    - exact twosided_disp_cat_of_lenses_put_axioms.
  Defined.

  Definition twosided_disp_cat_of_lawless_lenses
    : twosided_disp_cat C C
    := prod_of_twosided_disp_cat
         twosided_disp_cat_of_lenses_get
         twosided_disp_cat_of_lenses_put.

  Definition lenses_laws
             {s v : C}
             (l : twosided_disp_cat_of_lawless_lenses s v)
    : UU
    := let g := pr1 l in
       let p := pr2 l in
       (p · g = BinProductPr1 _ _)
       ×
       (BinProductArrow _ _ g (identity s) · p = identity s)
       ×
       (BinProductOfArrows
          _
          (prodC v _)
          (prodC _ _)
          (identity v)
          p
        · p
        =
        BinProductArrow
          _ _
          (BinProductPr1 _ _)
          (BinProductPr2 _ _ · BinProductPr2 _ _)
        · p).

  Definition disp_cat_of_lenses_laws
    : disp_cat
        (total_twosided_disp_category twosided_disp_cat_of_lawless_lenses).
  Proof.
    use (disp_full_sub).
    exact (λ x, lenses_laws (pr22 x)).
  Defined.

  Definition twosided_disp_cat_of_lenses
    : twosided_disp_cat C C
    := sigma_twosided_disp_cat
         twosided_disp_cat_of_lawless_lenses
         disp_cat_of_lenses_laws.

  (**
   2. Discreteness and univalence
   *)
  Definition lenses_get_twosided_disp_cat_is_iso
    : all_disp_mor_iso twosided_disp_cat_of_lenses_get.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - refine (!_).
      use z_iso_inv_on_right.
      rewrite assoc.
      use z_iso_inv_on_left ; cbn.
      exact (!fg).
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_lenses_get_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses_get.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_lenses_get_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses_get.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact lenses_get_twosided_disp_cat_is_iso.
    - exact is_univalent_lenses_get_twosided_disp_cat.
  Qed.

  Definition lenses_put_twosided_disp_cat_is_iso
    : all_disp_mor_iso twosided_disp_cat_of_lenses_put.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - refine (!_).
      use z_iso_inv_on_left ; cbn.
      rewrite !assoc'.
      rewrite fg.
      rewrite !assoc.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      rewrite BinProductOfArrows_comp.
      rewrite !z_iso_after_z_iso_inv.
      use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_lenses_put_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses_put.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_right in p.
      refine (p @ _ @ id_left _).
      apply maponpaths_2.
      refine (!_).
      use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_lenses_put_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses_put.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact lenses_put_twosided_disp_cat_is_iso.
    - exact is_univalent_lenses_put_twosided_disp_cat.
  Qed.

  Definition is_univalent_lenses_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_prod_of_twosided_disp_cat.
      + exact is_univalent_lenses_get_twosided_disp_cat.
      + exact is_univalent_lenses_put_twosided_disp_cat.
    - abstract
        (use disp_full_sub_univalent ;
         intro x ;
         repeat (apply isapropdirprod) ; apply homset_property).
  Defined.

  Definition discrete_lenses_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses.
  Proof.
    use discrete_sigma_twosided_disp_cat.
    - use discrete_prod_twosided_disp_cat.
      + exact discrete_lenses_get_twosided_disp_cat.
      + exact discrete_lenses_put_twosided_disp_cat.
    - abstract
        (use disp_full_sub_univalent ;
         intro x ;
         repeat (apply isapropdirprod) ; apply homset_property).
    - intro ; intros.
      apply isapropunit.
    - abstract
        (intro ; intros ;
         simple refine (tt ,, _ ,, _) ; apply isapropunit).
  Defined.
End Lenses.
