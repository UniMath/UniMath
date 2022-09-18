(**********************************************************************************

 Limits in subbicategories

 We look at limits in subbicategories where 0-cells and 1-cells are selected.
 These can be constructed from limits in the original bicategory if some conditions
 are satisfied.

 1. Final objects
 2. Products
 3. Pullbacks

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.TotalBicategoryLimits.

Local Open Scope cat.

Section LimitsSubbicat.
  Context {B : bicat}
          (P₀ : B → UU)
          (P₁ : ∏ (x y : B), x --> y → UU)
          (Pid : ∏ (x : B), P₁ x x (id₁ x))
          (Pcomp : ∏ (x y z : B)
                     (f : x --> y)
                     (g : y --> z),
              P₁ x y f → P₁ y z g → P₁ x z (f · g)).

  Definition subbicat_disp_2cell_over
             {x y : B}
             {f g : x --> y}
             (α : f ==> g)
             {xx : disp_subbicat P₀ P₁ Pid Pcomp x}
             {yy : disp_subbicat P₀ P₁ Pid Pcomp y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g] yy}
    : ff ==>[ α ] gg
    := tt ,, tt.

  (**
   1. Final objects
   *)
  Definition subbicat_disp_final
             (HB : bifinal_obj B)
             (P_final : P₀ (pr1 HB))
             (P_mor : ∏ (x : subbicat P₀ P₁ Pid Pcomp),
                      P₁ _ _ (is_bifinal_1cell_property (pr2 HB) (pr1 x)))
    : disp_bifinal_obj (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    simple refine (_ ,, _).
    - exact (tt ,, P_final).
    - exact (λ x xx, P_mor (x ,, xx) ,, tt).
  Defined.

  Definition subbicat_final
             (HB : bifinal_obj B)
             (P_final : P₀ (pr1 HB))
             (P_mor : ∏ (x : subbicat P₀ P₁ Pid Pcomp),
                      P₁ _ _ (is_bifinal_1cell_property (pr2 HB) (pr1 x)))
    : bifinal_obj (subbicat P₀ P₁ Pid Pcomp).
  Proof.
    use total_bicat_final.
    - apply disp_2cells_isaprop_subbicat.
    - intros.
      apply subbicat_disp_2cell_over.
    - exact HB.
    - exact (subbicat_disp_final HB P_final P_mor).
  Defined.

  (**
   2. Products
   *)
  Definition subbicat_disp_binprod
             (HB : has_binprod B)
             (Hcone : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                      P₀ (pr1 (HB (pr1 x) (pr1 y))))
             (Hπ₁ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _ (binprod_cone_pr1 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hπ₂ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _ (binprod_cone_pr2 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hpair : ∏ (x y : subbicat P₀ P₁ Pid Pcomp)
                        (q : binprod_cone x y),
                      P₁ _ _
                        (binprod_ump_1cell
                           (pr2 (HB (pr1 x) (pr1 y)))
                           (pr1 (binprod_cone_pr1 q))
                           (pr1 (binprod_cone_pr2 q))))
    : disp_has_binprod (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    intros x y.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (tt ,, Hcone x y).
    - exact (Hπ₁ x y ,, tt).
    - exact (Hπ₂ x y ,, tt).
    - exact (λ z f g, Hpair x y (make_binprod_cone z f g) ,, tt).
  Defined.

  Definition subbicat_binprod
             (HB : has_binprod B)
             (HB' : is_univalent_2 B)
             (Hcone : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                      P₀ (pr1 (HB (pr1 x) (pr1 y))))
             (Hπ₁ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _ (binprod_cone_pr1 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hπ₂ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _ (binprod_cone_pr2 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hpair : ∏ (x y : subbicat P₀ P₁ Pid Pcomp)
                        (q : binprod_cone x y),
                      P₁ _ _
                        (binprod_ump_1cell
                           (pr2 (HB (pr1 x) (pr1 y)))
                           (pr1 (binprod_cone_pr1 q))
                           (pr1 (binprod_cone_pr2 q))))
    : has_binprod (subbicat P₀ P₁ Pid Pcomp).
  Proof.
    use total_bicat_prod.
    - apply disp_2cells_isaprop_subbicat.
    - intros.
      apply subbicat_disp_2cell_over.
    - use disp_locally_groupoid_subbicat.
      exact HB'.
    - exact HB.
    - apply subbicat_disp_binprod.
      + exact Hcone.
      + exact Hπ₁.
      + exact Hπ₂.
      + exact Hpair.
  Defined.

  (**
   3. Pullbacks
   *)
  Definition subbicat_disp_has_pb
             (HB : has_pb B)
             (Hcone : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                        (f : x --> z)
                        (g : y --> z),
                      P₀ (pr1 (HB _ _ _ (pr1 f) (pr1 g))))
             (Hπ₁ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _ (pb_cone_pr1 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (Hπ₂ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _ (pb_cone_pr2 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (H_ump_mor : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                            (f : x --> z)
                            (g : y --> z)
                            (q : pb_cone f g),
                          P₁ _ _
                            (pb_ump_mor
                               (pr2 (HB (pr1 x) (pr1 y) (pr1 z) (pr1 f) (pr1 g)))
                               (total_pb_cone_help_cone _ q)))
    : disp_has_pb (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    intros x y z f g.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (tt ,, Hcone x y z f g).
    - exact (Hπ₁ x y z f g ,, tt).
    - exact (Hπ₂ x y z f g ,, tt).
    - exact (λ q, H_ump_mor x y z f g q ,, tt).
  Defined.

  Definition subbicat_has_pb
             (HB : has_pb B)
             (HB' : is_univalent_2 B)
             (Hcone : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                        (f : x --> z)
                        (g : y --> z),
                      P₀ (pr1 (HB _ _ _ (pr1 f) (pr1 g))))
             (Hπ₁ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _ (pb_cone_pr1 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (Hπ₂ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _ (pb_cone_pr2 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (H_ump_mor : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                            (f : x --> z)
                            (g : y --> z)
                            (q : pb_cone f g),
                          P₁ _ _
                            (pb_ump_mor
                               (pr2 (HB (pr1 x) (pr1 y) (pr1 z) (pr1 f) (pr1 g)))
                               (total_pb_cone_help_cone _ q)))
    : has_pb (subbicat P₀ P₁ Pid Pcomp).
  Proof.
    use total_bicat_has_pb.
    - apply disp_2cells_isaprop_subbicat.
    - intros.
      apply subbicat_disp_2cell_over.
    - use disp_locally_groupoid_subbicat.
      exact HB'.
    - exact HB.
    - apply subbicat_disp_has_pb.
      + exact Hcone.
      + exact Hπ₁.
      + exact Hπ₂.
      + exact H_ump_mor.
  Defined.
End LimitsSubbicat.
