(***********************************************************************

 Subbicategories

 We consider two ways of constructing subbicategories. One by selecting
 1-cells and one by selecting both 0-cells and 1-cells.

 Contents
 1. Subbicategory by selecting 1-cells
 2. Subbicategory by selecting both 0-cells and 1-cells

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.

(**
 1. Subbicategory by selecting 1-cells
 *)
Section Sub1CellBicategory.
  Context (B : bicat)
          (P : ∏ (x y : B), x --> y -> UU)
          (Pid : ∏ (x : B), P _ _ (id₁ x))
          (Pcomp : ∏ (x y z : B) (f : x --> y) (g : y --> z),
                   P  _ _ f → P _ _ g → P _ _ (f · g)).

  Definition disp_sub1cell_disp_cat
    : disp_cat_ob_mor B.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ _, unit).
    - exact (λ _ _ _ _ f, P _ _ f).
  Defined.

  Definition disp_sub1cell_disp_cat_id_comp
    : disp_cat_id_comp _ disp_sub1cell_disp_cat.
  Proof.
    use tpair.
    - exact (λ _ _, Pid _).
    - exact (λ _ _ _ _ _ _ _ _ p q, Pcomp _ _ _ _ _ p q).
  Defined.

  Definition disp_sub1cell_disp_cat_data
    : disp_cat_data B.
  Proof.
    use tpair.
    - exact disp_sub1cell_disp_cat.
    - exact disp_sub1cell_disp_cat_id_comp.
  Defined.

  Definition disp_sub1cell_prebicat : disp_prebicat B
    := disp_cell_unit_bicat disp_sub1cell_disp_cat_data.

  Definition disp_sub1cell_bicat : disp_bicat B
    := disp_cell_unit_bicat disp_sub1cell_disp_cat_data.

  Definition disp_2cells_isaprop_sub1cell_bicat    : disp_2cells_isaprop disp_sub1cell_bicat.
  Proof.
    apply disp_2cells_isaprop_cell_unit_bicat.
  Defined.

  Definition disp_locally_groupoid_sub1cell_bicat
    : disp_locally_groupoid disp_sub1cell_bicat.
  Proof.
    apply disp_locally_groupoid_cell_unit_bicat.
  Defined.

  Definition disp_sub1cell_univalent_2_1
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : disp_univalent_2_1 disp_sub1cell_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply HP.
  Defined.

  Definition disp_sub1cell_univalent_2_0
             (HB : is_univalent_2_1 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : disp_univalent_2_0 disp_sub1cell_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - exact HB.
    - intros ; apply HP.
    - simpl ; intro.
      apply isasetunit.
    - simpl.
      intros.
      apply isapropunit.
  Qed.

  Definition disp_sub1cell_univalent_2
             (HB : is_univalent_2_1 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : disp_univalent_2 disp_sub1cell_bicat.
  Proof.
    split.
    - use disp_sub1cell_univalent_2_0.
      + exact HB.
      + exact HP.
    - use disp_sub1cell_univalent_2_1.
      exact HP.
  Defined.

  Definition sub1cell_bicat
    : bicat
    := total_bicat disp_sub1cell_bicat.

  Definition is_univalent_2_1_sub1cell_bicat
             (HB : is_univalent_2_1 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : is_univalent_2_1 sub1cell_bicat.
  Proof.
    use total_is_univalent_2_1.
    - exact HB.
    - use disp_sub1cell_univalent_2_1.
      exact HP.
  Defined.

  Definition is_univalent_2_0_sub1cell_bicat
             (HB : is_univalent_2 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : is_univalent_2_0 sub1cell_bicat.
  Proof.
    use total_is_univalent_2_0.
    - exact (pr1 HB).
    - use disp_sub1cell_univalent_2_0.
      + exact (pr2 HB).
      + exact HP.
  Defined.

  Definition is_univalent_2_sub1cell_bicat
             (HB : is_univalent_2 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : is_univalent_2 sub1cell_bicat.
  Proof.
    split.
    - use is_univalent_2_0_sub1cell_bicat.
      + exact HB.
      + exact HP.
    - use is_univalent_2_1_sub1cell_bicat.
      + exact (pr2 HB).
      + exact HP.
  Defined.
End Sub1CellBicategory.

(**
 2. Subbicategory by selecting both 0-cells and 1-cells
 *)
Section SubBicategory.
  Context {B : bicat}
          (P₀ : B → UU)
          (P₁ : ∏ (x y : B), x --> y -> UU)
          (P₁id : ∏ (x : B), P₁ _ _ (id₁ x))
          (P₁comp : ∏ (x y z : B) (f : x --> y) (g : y --> z),
              P₁  _ _ f → P₁ _ _ g → P₁ _ _ (f · g)).

  Definition disp_subbicat : disp_bicat B
    := sigma_bicat
         B
         (disp_sub1cell_bicat B P₁ P₁id P₁comp)
         (disp_fullsubbicat
            (total_bicat (disp_sub1cell_bicat B P₁ P₁id P₁comp))
            (λ z, P₀ (pr1 z))).

  Definition disp_2cells_isaprop_subbicat
    : disp_2cells_isaprop disp_subbicat.
  Proof.
    apply disp_2cells_isaprop_sigma.
    - apply disp_2cells_isaprop_sub1cell_bicat.
    - apply disp_2cells_isaprop_fullsubbicat.
  Defined.

  Definition disp_locally_groupoid_subbicat
             (HB : is_univalent_2 B)
    : disp_locally_groupoid disp_subbicat.
  Proof.
    use disp_locally_groupoid_sigma.
    - exact HB.
    - apply disp_2cells_isaprop_sub1cell_bicat.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_locally_groupoid_sub1cell_bicat.
    - apply disp_locally_groupoid_fullsubbicat.
  Defined.

  Definition disp_subbicat_univalent_2_1
             (HP₁ : ∏ (x y : B) (f : x --> y), isaprop (P₁ x y f))
    : disp_univalent_2_1 disp_subbicat.
  Proof.
    use sigma_disp_univalent_2_1_with_props.
    - apply disp_2cells_isaprop_sub1cell_bicat.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_sub1cell_univalent_2_1.
      exact HP₁.
    - apply disp_fullsubbicat_univalent_2_1.
  Defined.

  Definition disp_subbicat_univalent_2_0
             (HB : is_univalent_2 B)
             (HP₀ : ∏ (x : B), isaprop (P₀ x))
             (HP₁ : ∏ (x y : B) (f : x --> y), isaprop (P₁ x y f))
    : disp_univalent_2_0 disp_subbicat.
  Proof.
    use sigma_disp_univalent_2_0_with_props.
    - exact HB.
    - apply disp_2cells_isaprop_sub1cell_bicat.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_sub1cell_univalent_2_1.
      exact HP₁.
    - apply disp_fullsubbicat_univalent_2_1.
    - apply disp_locally_groupoid_sub1cell_bicat.
    - apply disp_locally_groupoid_fullsubbicat.
    - apply disp_sub1cell_univalent_2_0.
      + apply HB.
      + exact HP₁.
    - use disp_univalent_2_0_fullsubbicat.
      + use total_is_univalent_2.
        * apply disp_sub1cell_univalent_2.
          ** apply HB.
          ** exact HP₁.
        * exact HB.
      + intro.
        apply HP₀.
  Defined.

  Definition subbicat
    : bicat
    := total_bicat disp_subbicat.

  Definition eq_2cell_subbicat
             {x y : subbicat}
             {f g : x --> y}
             {α β : f ==> g}
             (p : pr1 α = pr1 β)
    : α = β.
  Proof.
    use subtypePath.
    {
      intro.
      simpl.
      apply isapropdirprod ; apply isapropunit.
    }
    exact p.
  Qed.

  Definition is_invertible_2cell_subbicat
             {x y : subbicat}
             {f g : x --> y}
             (α : f ==> g)
             (Hα : is_invertible_2cell (pr1 α))
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - exact (Hα^-1 ,, tt ,, tt).
    - abstract
        (use eq_2cell_subbicat ;
         apply vcomp_rinv).
    - abstract
        (use eq_2cell_subbicat ;
         apply vcomp_linv).
  Defined.

  Definition invertible_2cell_subbicat
             {x y : subbicat}
             {f g : x --> y}
             (Hα : invertible_2cell (pr1 f) (pr1 g))
    : invertible_2cell f g.
  Proof.
    use make_invertible_2cell.
    - exact (pr1 Hα ,, tt ,, tt).
    - use is_invertible_2cell_subbicat.
      exact Hα.
  Defined.

  Definition from_is_invertible_2cell_subbicat
             {x y : subbicat}
             {f g : x --> y}
             (α : f ==> g)
             (Hα : is_invertible_2cell α)
    : is_invertible_2cell (pr1 α).
  Proof.
    use make_is_invertible_2cell.
    - exact (pr1 (Hα^-1)).
    - abstract
        (exact (maponpaths pr1 (vcomp_rinv Hα))).
    - abstract
        (exact (maponpaths pr1 (vcomp_linv Hα))).
  Defined.

  Definition from_invertible_2cell_subbicat
             {x y : subbicat}
             {f g : x --> y}
             (Hα : invertible_2cell f g)
    : invertible_2cell (pr1 f) (pr1 g).
  Proof.
    use make_invertible_2cell.
    - exact (pr11 Hα).
    - use from_is_invertible_2cell_subbicat.
      exact Hα.
  Defined.

  Definition is_univalent_2_1_subbicat
             (HB : is_univalent_2_1 B)
             (HP₁ : ∏ (x y : B) (f : x --> y), isaprop (P₁ x y f))
    : is_univalent_2_1 subbicat.
  Proof.
    use total_is_univalent_2_1.
    - exact HB.
    - use disp_subbicat_univalent_2_1.
      exact HP₁.
  Defined.

  Definition is_univalent_2_0_subbicat
             (HB : is_univalent_2 B)
             (HP₀ : ∏ (x : B), isaprop (P₀ x))
             (HP₁ : ∏ (x y : B) (f : x --> y), isaprop (P₁ x y f))
    : is_univalent_2_0 subbicat.
  Proof.
    use total_is_univalent_2_0.
    - exact (pr1 HB).
    - use disp_subbicat_univalent_2_0.
      + exact HB.
      + exact HP₀.
      + exact HP₁.
  Defined.

  Definition is_univalent_2_subbicat
             (HB : is_univalent_2 B)
             (HP₀ : ∏ (x : B), isaprop (P₀ x))
             (HP₁ : ∏ (x y : B) (f : x --> y), isaprop (P₁ x y f))
    : is_univalent_2 subbicat.
  Proof.
    split.
    - use is_univalent_2_0_subbicat.
      + exact HB.
      + exact HP₀.
      + exact HP₁.
    - use is_univalent_2_1_subbicat.
      + exact (pr2 HB).
      + exact HP₁.
  Defined.
End SubBicategory.
