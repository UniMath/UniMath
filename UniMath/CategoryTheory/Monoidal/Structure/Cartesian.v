(*********************************************************************************

 Cartesian and cocartesian monoidal categories

 In this file, we discuss several variations of cartesian monoidal categories. We
 also prove some properties about them.

 Contents
 1. Cartesan monoidal categories
 2. Cartesian monoidal categories are symmetric
 3. Cocartesian monoidal categories

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Cartesan monoidal categories
 *)
Definition is_semicartesian
           {C : category}
           (M : monoidal C)
  : UU
  := isTerminal C (I_{M}).

Section ProjectionsSemiCartesian.
  Context {M : monoidal_cat}
          (HM : is_semicartesian M).

  Definition semi_cart_to_unit
             (x : M)
    : x --> I_{M}
    := TerminalArrow (I_{M} ,, HM) x.

  Proposition semi_cart_to_unit_eq
              {x : M}
              (f g : x --> I_{M})
    : f = g.
  Proof.
    exact (@TerminalArrowEq _ (I_{M} ,, HM) x f g).
  Qed.

  Definition semi_cart_tensor_pr1
             (x y : M)
    : x ⊗ y --> x
    := identity _ #⊗ semi_cart_to_unit y · mon_runitor x.

  Definition semi_cart_tensor_pr2
             (x y : M)
    : x ⊗ y --> y
    := semi_cart_to_unit x #⊗ identity _ · mon_lunitor y.
End ProjectionsSemiCartesian.

Definition tensor_isBinProduct
           {M : monoidal_cat}
           (HM : is_semicartesian M)
  : UU
  := ∏ (x y : M),
     isBinProduct
       _ _ _ _
       (semi_cart_tensor_pr1 HM x y)
       (semi_cart_tensor_pr2 HM x y).

Definition is_cartesian
           (M : monoidal_cat)
  : UU
  := ∑ (HM : is_semicartesian M), tensor_isBinProduct HM.

#[reversible=no] Coercion is_cartesian_to_semicartesian
         {M : monoidal_cat}
         (M_cart : is_cartesian M)
  : is_semicartesian M
  := pr1 M_cart.

Definition is_cartesian_BinProduct
           {M : monoidal_cat}
           (M_cart : is_cartesian M)
           (x y : M)
  : BinProduct M x y
  := make_BinProduct _ _ _ _ _ _ (pr2 M_cart x y).

(**
 2. Cartesian monoidal categories are symmetric
 *)
Section CartesianSymmetric.
  Context {M : monoidal_cat}
          (M_cart : is_cartesian M).

  Definition cartesian_to_braiding_data
    : braiding_data M.
  Proof.
    intros x y.
    use (BinProductArrow _ (is_cartesian_BinProduct M_cart y x)).
    - apply (semi_cart_tensor_pr2 M_cart).
    - apply (semi_cart_tensor_pr1 M_cart).
  Defined.

  Proposition cartesian_to_braiding_data_pr1
              (x y : M)
    : cartesian_to_braiding_data x y
      · semi_cart_tensor_pr1 (pr1 M_cart) y x
      =
      semi_cart_tensor_pr2 M_cart x y.
  Proof.
    apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct M_cart y x)).
  Qed.

  Proposition cartesian_to_braiding_data_pr2
              (x y : M)
    : cartesian_to_braiding_data x y
      · semi_cart_tensor_pr2 (pr1 M_cart) y x
      =
      semi_cart_tensor_pr1 M_cart x y.
  Proof.
    apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct M_cart y x)).
  Qed.

  Proposition cartesian_tensor_pr1
              {x₁ x₂ y₁ y₂ : M}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : f #⊗ g · semi_cart_tensor_pr1 M_cart x₂ y₂
      =
      semi_cart_tensor_pr1 M_cart x₁ y₁ · f.
  Proof.
    unfold semi_cart_tensor_pr1.
    rewrite !assoc'.
    rewrite <- tensor_runitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_mor.
    rewrite !id_left, !id_right.
    apply maponpaths.
    apply (semi_cart_to_unit_eq M_cart).
  Qed.

  Proposition cartesian_tensor_pr2
              {x₁ x₂ y₁ y₂ : M}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : f #⊗ g · semi_cart_tensor_pr2 M_cart x₂ y₂
      =
      semi_cart_tensor_pr2 M_cart x₁ y₁ · g.
  Proof.
    unfold semi_cart_tensor_pr2.
    rewrite !assoc'.
    rewrite <- tensor_lunitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_mor.
    rewrite !id_left, !id_right.
    apply maponpaths_2.
    apply (semi_cart_to_unit_eq M_cart).
  Qed.

  Proposition cartesian_tensor_mor
              {x₁ x₂ y₁ y₂ : M}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : f #⊗ g
      =
      BinProductOfArrows
        _
        (is_cartesian_BinProduct M_cart x₂ y₂)
        (is_cartesian_BinProduct M_cart x₁ y₁)
        f
        g.
  Proof.
    use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct M_cart _ _)).
    - refine (!_).
      etrans.
      {
        apply (BinProductOfArrowsPr1
                 _
                 (is_cartesian_BinProduct M_cart x₂ y₂)
                 (is_cartesian_BinProduct M_cart x₁ y₁)).
      }
      cbn.
      rewrite cartesian_tensor_pr1.
      apply idpath.
    - refine (!_).
      etrans.
      {
        apply (BinProductOfArrowsPr2
                 _
                 (is_cartesian_BinProduct M_cart x₂ y₂)
                 (is_cartesian_BinProduct M_cart x₁ y₁)).
      }
      cbn.
      rewrite cartesian_tensor_pr2.
      apply idpath.
  Qed.

  Proposition mon_lunitor_pr1
              (x y : M)
    : mon_lunitor (x ⊗ y) · semi_cart_tensor_pr1 M_cart _ _
      =
      identity _ #⊗ semi_cart_tensor_pr1 M_cart _ _ · mon_lunitor x.
  Proof.
    rewrite tensor_lunitor.
    apply idpath.
  Qed.

  Proposition mon_lunitor_pr2
              (x y : M)
    : mon_lunitor (x ⊗ y) · semi_cart_tensor_pr2 M_cart _ _
      =
      identity _ #⊗ semi_cart_tensor_pr2 M_cart _ _ · mon_lunitor y.
  Proof.
    rewrite tensor_lunitor.
    apply idpath.
  Qed.

  Proposition mon_runitor_pr1
              (x y : M)
    : mon_runitor (x ⊗ y) · semi_cart_tensor_pr1 M_cart _ _
      =
      semi_cart_tensor_pr1 M_cart _ _ #⊗ identity _ · mon_runitor x.
  Proof.
    rewrite tensor_runitor.
    apply idpath.
  Qed.

  Proposition mon_runitor_pr2
              (x y : M)
    : mon_runitor (x ⊗ y) · semi_cart_tensor_pr2 M_cart _ _
      =
      semi_cart_tensor_pr2 M_cart _ _ #⊗ identity _ · mon_runitor y.
  Proof.
    rewrite tensor_runitor.
    apply idpath.
  Qed.

  Proposition mon_lassociator_pr1
              (x y z : M)
    : mon_lassociator x y z · semi_cart_tensor_pr1 M_cart _ _
      =
      semi_cart_tensor_pr1 M_cart _ _ · semi_cart_tensor_pr1 M_cart _ _.
  Proof.
    unfold semi_cart_tensor_pr1.
    rewrite !assoc.
    apply maponpaths_2.
    refine (_ @ id_left _).
    rewrite <- mon_lassociator_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite <- tensor_rassociator.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_runitor_triangle.
      apply idpath.
    }
    rewrite <- !tensor_comp_id_l.
    apply maponpaths.
    apply (semi_cart_to_unit_eq M_cart).
  Qed.

  Proposition mon_lassociator_pr2
              (x y z : M)
    : mon_lassociator x y z
      · semi_cart_tensor_pr2 M_cart x (y ⊗ z)
      =
      semi_cart_tensor_pr2 M_cart x y #⊗ identity _.
  Proof.
    unfold semi_cart_tensor_pr2.
    rewrite <- tensor_id_id.
    rewrite !assoc.
    rewrite <- tensor_lassociator.
    rewrite !assoc'.
    rewrite mon_lunitor_triangle.
    rewrite !tensor_comp_id_r.
    apply idpath.
  Qed.

  Proposition cartesian_to_symmetric_laws
    : sym_mon_cat_laws_tensored M cartesian_to_braiding_data.
  Proof.
    repeat split.
    - intros x y.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct M_cart x y)).
      + rewrite !assoc' ; cbn.
        etrans.
        {
          apply maponpaths.
          apply cartesian_to_braiding_data_pr1.
        }
        rewrite id_left.
        apply cartesian_to_braiding_data_pr2.
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply cartesian_to_braiding_data_pr2.
        }
        rewrite id_left.
        apply cartesian_to_braiding_data_pr1.
    - intros x₁ x₂ y₁ y₂ f g.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct M_cart _ _)).
      + rewrite !assoc' ; cbn.
        etrans.
        {
          apply maponpaths.
          apply cartesian_to_braiding_data_pr1.
        }
        rewrite cartesian_tensor_pr2.
        rewrite cartesian_tensor_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply cartesian_to_braiding_data_pr1.
      + rewrite !assoc' ; cbn.
        etrans.
        {
          apply maponpaths.
          apply cartesian_to_braiding_data_pr2.
        }
        rewrite cartesian_tensor_pr2.
        rewrite cartesian_tensor_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply cartesian_to_braiding_data_pr2.
    - intros x y z.
      use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct M_cart _ _)) ; cbn.
      + rewrite !assoc'.
        rewrite cartesian_tensor_pr1.
        rewrite id_right.
        rewrite !mon_lassociator_pr1.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          apply cartesian_to_braiding_data_pr1.
        }
        refine (!_).
        rewrite !assoc.
        rewrite cartesian_tensor_pr1.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply cartesian_to_braiding_data_pr1.
        }
        rewrite !assoc.
        rewrite mon_lassociator_pr2.
        rewrite cartesian_tensor_pr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite mon_lassociator_pr2.
        rewrite cartesian_tensor_pr2.
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        rewrite mon_lassociator_pr2.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply cartesian_to_braiding_data_pr2.
        }
        use (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct M_cart _ _)) ; cbn.
        * rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply cartesian_to_braiding_data_pr1.
          }
          rewrite cartesian_tensor_pr2.
          rewrite id_right.
          rewrite cartesian_tensor_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            apply cartesian_to_braiding_data_pr1.
          }
          rewrite !assoc.
          rewrite mon_lassociator_pr2.
          rewrite cartesian_tensor_pr2.
          rewrite id_right.
          apply idpath.
        * rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply cartesian_to_braiding_data_pr2.
          }
          rewrite cartesian_tensor_pr2.
          rewrite id_right.
          rewrite cartesian_tensor_pr1.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply cartesian_to_braiding_data_pr2.
          }
          rewrite mon_lassociator_pr1.
          apply idpath.
  Qed.

  Definition cartesian_to_symmetric
    : symmetric M.
  Proof.
    use make_symmetric.
    - exact cartesian_to_braiding_data.
    - exact cartesian_to_symmetric_laws.
  Defined.
End CartesianSymmetric.

(**
 3. Cocartesian monoidal categories
 *)
Definition is_semicocartesian
           {C : category}
           (M : monoidal C)
  : UU
  := isInitial C (I_{M}).

Section ProjectionsSemiCocartesian.
  Context {M : monoidal_cat}
          (HM : is_semicocartesian M).

  Definition semi_cocart_to_unit
             (x : M)
    : I_{M} --> x
    := InitialArrow (I_{M} ,, HM) x.

  Proposition semi_cocart_from_unit_eq
              {x : M}
              (f g : I_{M} --> x)
    : f = g.
  Proof.
    exact (@InitialArrowEq _ (I_{M} ,, HM) x f g).
  Qed.

  Definition semi_cocart_tensor_inl
             (x y : M)
    : x --> x ⊗ y
    := mon_rinvunitor x · identity _ #⊗ semi_cocart_to_unit y.

  Definition semi_cocart_tensor_inr
             (x y : M)
    : y --> x ⊗ y
    := mon_linvunitor y · semi_cocart_to_unit x #⊗ identity _.
End ProjectionsSemiCocartesian.

Definition tensor_isBinCoproduct
           {M : monoidal_cat}
           (HM : is_semicocartesian M)
  : UU
  := ∏ (x y : M),
     isBinCoproduct
       _ _ _ _
       (semi_cocart_tensor_inl HM x y)
       (semi_cocart_tensor_inr HM x y).

Definition is_cocartesian
           (M : monoidal_cat)
  : UU
  := ∑ (HM : is_semicocartesian M), tensor_isBinCoproduct HM.

#[reversible=no] Coercion is_cocartesian_to_semicocartesian
         {M : monoidal_cat}
         (M_cocart : is_cocartesian M)
  : is_semicocartesian M
  := pr1 M_cocart.

Definition is_cartesian_BinCoproduct
           {M : monoidal_cat}
           (M_cocart : is_cocartesian M)
           (x y : M)
  : BinCoproduct x y
  := make_BinCoproduct _ _ _ _ _ _ (pr2 M_cocart x y).
