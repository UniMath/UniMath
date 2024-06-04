(*******************************************************************************************

 The product of displayed biequivalences

 If we have two displayed bicategories `D₁` and `D₃` over a bicategory `B`, then we can take
 their product `D₁ × D₃`, which is a displayed bicategory over `B`. If `D₁` is biequivalent
 to `D₂` and `D₃` is biequivalent to `D₄`, then the products `D₁ × D₃` and `D₂ × D₃` are
 biequivalent as well. We prove that in this file under the assumption that all displayed
 2-cells in the involved displayed bicategories are equal and invertible.

 Contents
 1. The product of displayed pseudofunctors
 2. The product of displayed biequivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

(** * 1. The product of displayed pseudofunctors *)
Definition prod_disp_psfunctor
           {B₁ B₂ : bicat}
           {D₁ D₃ : disp_bicat B₁}
           {D₂ D₄ : disp_bicat B₂}
           (HD₂ : disp_2cells_isaprop D₂)
           (HD₂' : disp_locally_groupoid D₂)
           (HD₄ : disp_2cells_isaprop D₄)
           (HD₄' : disp_locally_groupoid D₄)
           {F : psfunctor B₁ B₂}
           (FF₁ : disp_psfunctor D₁ D₂ F)
           (FF₂ : disp_psfunctor D₃ D₄ F)
  : disp_psfunctor
      (disp_dirprod_bicat D₁ D₃)
      (disp_dirprod_bicat D₂ D₄)
      F.
Proof.
  use make_disp_psfunctor.
  - use disp_2cells_isaprop_prod.
    + exact HD₂.
    + exact HD₄.
  - use disp_locally_groupoid_prod.
    + exact HD₂'.
    + exact HD₄'.
  - exact (λ x xx, FF₁ x (pr1 xx) ,, FF₂ x (pr2 xx)).
  - exact (λ x y f xx yy ff, ♯ FF₁ (pr1 ff) ,, ♯ FF₂ (pr2 ff)).
  - exact (λ x y f g τ xx yy ff gg ττ, ♯♯ FF₁ (pr1 ττ) ,, ♯♯ FF₂ (pr2 ττ)).
  - refine (λ x xx, _ ,, _).
    + exact (disp_psfunctor_id _ _ _ FF₁ (pr1 xx)).
    + exact (disp_psfunctor_id _ _ _ FF₂ (pr2 xx)).
  - refine (λ x y z f g xx yy zz ff gg, _ ,, _).
    + exact (disp_psfunctor_comp _ _ _ FF₁ (pr1 ff) (pr1 gg)).
    + exact (disp_psfunctor_comp _ _ _ FF₂ (pr2 ff) (pr2 gg)).
Defined.

(** * 2. The product of displayed biequivalences *)
Section ProdDispBiequiv.
  Context {B₁ B₂ : bicat}
          {D₁ D₃ : disp_bicat B₁}
          {D₂ D₄ : disp_bicat B₂}
          (HD₁ : disp_2cells_isaprop D₁)
          (HD₁' : disp_locally_groupoid D₁)
          (HD₂ : disp_2cells_isaprop D₂)
          (HD₂' : disp_locally_groupoid D₂)
          (HD₃ : disp_2cells_isaprop D₃)
          (HD₃' : disp_locally_groupoid D₃)
          (HD₄ : disp_2cells_isaprop D₄)
          (HD₄' : disp_locally_groupoid D₄)
          {L : psfunctor B₁ B₂}
          {R : psfunctor B₂ B₁}
          (εη : is_biequivalence_unit_counit L R)
          (invs : is_biequivalence_adjoints εη)
          (LL₁ : disp_psfunctor D₁ D₂ L)
          (LL₂ : disp_psfunctor D₃ D₄ L)
          (RR₁ : disp_psfunctor D₂ D₁ R)
          (RR₂ : disp_psfunctor D₄ D₃ R)
          (εηεη₁ : is_disp_biequivalence_unit_counit D₁ D₂ εη LL₁ RR₁)
          (εηεη₂ : is_disp_biequivalence_unit_counit D₃ D₄ εη LL₂ RR₂)
          (H₁ : disp_is_biequivalence_data D₁ D₂ invs εηεη₁)
          (H₂ : disp_is_biequivalence_data D₃ D₄ invs εηεη₂).

  Let LLprod
    : disp_psfunctor
        (disp_dirprod_bicat D₁ D₃)
        (disp_dirprod_bicat D₂ D₄)
      L
    := prod_disp_psfunctor HD₂ HD₂' HD₄ HD₄' LL₁ LL₂.

  Let RRprod
    : disp_psfunctor
        (disp_dirprod_bicat D₂ D₄)
        (disp_dirprod_bicat D₁ D₃)
      R
    := prod_disp_psfunctor HD₁ HD₁' HD₃ HD₃' RR₁ RR₂.

  Definition prod_unit_of_is_biequvalence
    : disp_pstrans
        (disp_pseudo_comp _ _ _ _ _ LLprod RRprod)
        (disp_pseudo_id (disp_dirprod_bicat D₁ D₃))
        (unit_of_is_biequivalence εη).
  Proof.
    use make_disp_pstrans.
    - use disp_2cells_isaprop_prod.
      + exact HD₁.
      + exact HD₃.
    - use disp_locally_groupoid_prod.
      + exact HD₁'.
      + exact HD₃'.
    - refine (λ x xx, _ ,, _).
      + exact (unit_of_is_disp_biequivalence _ _ εηεη₁ x (pr1 xx)).
      + exact (unit_of_is_disp_biequivalence _ _ εηεη₂ x (pr2 xx)).
    - refine (λ x y f xx yy ff, _ ,, _).
      + exact (disp_psnaturality_of
                 _ _ _
                 (unit_of_is_disp_biequivalence _ _ εηεη₁)
                 (pr1 ff)).
      + exact (disp_psnaturality_of
                 _ _ _
                 (unit_of_is_disp_biequivalence _ _ εηεη₂)
                 (pr2 ff)).
  Defined.

  Definition prod_counit_of_is_biequvalence
    : disp_pstrans
        (disp_pseudo_comp _ _ _ _ _ RRprod LLprod)
        (disp_pseudo_id (disp_dirprod_bicat D₂ D₄))
        (counit_of_is_biequivalence εη).
  Proof.
    use make_disp_pstrans.
    - use disp_2cells_isaprop_prod.
      + exact HD₂.
      + exact HD₄.
    - use disp_locally_groupoid_prod.
      + exact HD₂'.
      + exact HD₄'.
    - refine (λ x xx, _ ,, _).
      + exact (counit_of_is_disp_biequivalence _ _ εηεη₁ x (pr1 xx)).
      + exact (counit_of_is_disp_biequivalence _ _ εηεη₂ x (pr2 xx)).
    - refine (λ x y f xx yy ff, _ ,, _).
      + exact (disp_psnaturality_of
                 _ _ _
                 (counit_of_is_disp_biequivalence _ _ εηεη₁)
                 (pr1 ff)).
      + exact (disp_psnaturality_of
                 _ _ _
                 (counit_of_is_disp_biequivalence _ _ εηεη₂)
                 (pr2 ff)).
  Defined.

  Definition prod_is_disp_biequivalence_unit_counit
    : is_disp_biequivalence_unit_counit
        (disp_dirprod_bicat D₁ D₃)
        (disp_dirprod_bicat D₂ D₄)
        εη
        LLprod
        RRprod.
  Proof.
    split.
    - exact prod_unit_of_is_biequvalence.
    - exact prod_counit_of_is_biequvalence.
  Defined.

  Definition prod_unit_inv_of_is_biequvalence
    : disp_pstrans
        (disp_pseudo_id (disp_dirprod_bicat D₁ D₃))
        (disp_pseudo_comp _ _ _ _ _ LLprod RRprod)
        (invunit_of_is_biequivalence invs).
  Proof.
    use make_disp_pstrans.
    - use disp_2cells_isaprop_prod.
      + exact HD₁.
      + exact HD₃.
    - use disp_locally_groupoid_prod.
      + exact HD₁'.
      + exact HD₃'.
    - refine (λ x xx, _ ,, _).
      + exact (pr1 H₁ x (pr1 xx)).
      + exact (pr1 H₂ x (pr2 xx)).
    - refine (λ x y f xx yy ff, _ ,, _).
      + exact (disp_psnaturality_of
                 _ _ _
                 (pr1 H₁)
                 (pr1 ff)).
      + exact (disp_psnaturality_of
                 _ _ _
                 (pr1 H₂)
                 (pr2 ff)).
  Defined.

  Definition prod_counit_inv_of_is_biequvalence
    : disp_pstrans
        (disp_pseudo_id (disp_dirprod_bicat D₂ D₄))
        (disp_pseudo_comp _ _ _ _ _ RRprod LLprod)
        (invcounit_of_is_biequivalence invs).
  Proof.
    use make_disp_pstrans.
    - use disp_2cells_isaprop_prod.
      + exact HD₂.
      + exact HD₄.
    - use disp_locally_groupoid_prod.
      + exact HD₂'.
      + exact HD₄'.
    - refine (λ x xx, _ ,, _).
      + exact (pr12 H₁ x (pr1 xx)).
      + exact (pr12 H₂ x (pr2 xx)).
    - refine (λ x y f xx yy ff, _ ,, _).
      + exact (disp_psnaturality_of
                 _ _ _
                 (pr12 H₁)
                 (pr1 ff)).
      + exact (disp_psnaturality_of
                 _ _ _
                 (pr12 H₂)
                 (pr2 ff)).
  Defined.

  Definition prod_disp_is_biequivalence_data
    : disp_is_biequivalence_data
        (disp_dirprod_bicat D₁ D₃)
        (disp_dirprod_bicat D₂ D₄)
        invs
        prod_is_disp_biequivalence_unit_counit.
  Proof.
    simple refine (_ ,, _ ,, (_ ,, _) ,, (_ ,, _)).
    - exact prod_unit_inv_of_is_biequvalence.
    - exact prod_counit_inv_of_is_biequvalence.
    - use make_disp_invmodification.
      + use disp_2cells_isaprop_prod.
        * exact HD₁.
        * exact HD₃.
      + use disp_locally_groupoid_prod.
        * exact HD₁'.
        * exact HD₃'.
      + refine (λ x xx, _ ,, _).
        * exact (pr11 (pr122 H₁) x (pr1 xx)).
        * exact (pr11 (pr122 H₂) x (pr2 xx)).
    - use make_disp_invmodification.
      + use disp_2cells_isaprop_prod.
        * exact HD₁.
        * exact HD₃.
      + use disp_locally_groupoid_prod.
        * exact HD₁'.
        * exact HD₃'.
      + refine (λ x xx, _ ,, _).
        * exact (pr12 (pr122 H₁) x (pr1 xx)).
        * exact (pr12 (pr122 H₂) x (pr2 xx)).
    - use make_disp_invmodification.
      + use disp_2cells_isaprop_prod.
        * exact HD₂.
        * exact HD₄.
      + use disp_locally_groupoid_prod.
        * exact HD₂'.
        * exact HD₄'.
      + refine (λ x xx, _ ,, _).
        * exact (pr11 (pr222 H₁) x (pr1 xx)).
        * exact (pr11 (pr222 H₂) x (pr2 xx)).
    - use make_disp_invmodification.
      + use disp_2cells_isaprop_prod.
        * exact HD₂.
        * exact HD₄.
      + use disp_locally_groupoid_prod.
        * exact HD₂'.
        * exact HD₄'.
      + refine (λ x xx, _ ,, _).
        * exact (pr12 (pr222 H₁) x (pr1 xx)).
        * exact (pr12 (pr222 H₂) x (pr2 xx)).
  Defined.
End ProdDispBiequiv.
