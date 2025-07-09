(**********************************************************************************

 Limits in subbicategories

 We look at limits in subbicategories where 0-cells and 1-cells are selected.
 These can be constructed from limits in the original bicategory if some conditions
 are satisfied.

 1. Final objects
 2. Products
 3. Pullbacks
 4. Eilenberg-Moore categories

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Limits.Examples.TotalBicategoryLimits.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInTotalBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

Section LimitsSubbicat.
  Context {B : bicat}
          (P₀ : B → UU)
          (P₁ : ∏ (x y : B), P₀ x → P₀ y → x --> y → UU)
          (Pid : ∏ (x : B) (Px : P₀ x), P₁ x x Px Px (id₁ x))
          (Pcomp : ∏ (x y z : B)
                     (Px : P₀ x)
                     (Py : P₀ y)
                     (Pz : P₀ z)
                     (f : x --> y)
                     (g : y --> z),
              P₁ x y Px Py f → P₁ y z Py Pz g → P₁ x z Px Pz (f · g)).

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
                      P₁ _ _ (pr12 x) P_final (is_bifinal_1cell_property (pr2 HB) (pr1 x)))
    : disp_bifinal_obj (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    simple refine (_ ,, _).
    - exact (P_final ,, tt).
    - exact (λ x xx, tt ,, P_mor (x ,, xx)).
  Defined.

  Definition subbicat_final
             (HB : bifinal_obj B)
             (P_final : P₀ (pr1 HB))
             (P_mor : ∏ (x : subbicat P₀ P₁ Pid Pcomp),
                      P₁ _ _ (pr12 x) P_final (is_bifinal_1cell_property (pr2 HB) (pr1 x)))
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
                    P₁ _ _
                      (Hcone x y)
                      (pr12 x)
                      (binprod_cone_pr1 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hπ₂ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _
                      (Hcone x y)
                      (pr12 y)
                      (binprod_cone_pr2 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hpair : ∏ (x y : subbicat P₀ P₁ Pid Pcomp)
                        (q : binprod_cone x y),
                      P₁ _ _
                         (pr121 q)
                         (Hcone x y)
                         (binprod_ump_1cell
                            (pr2 (HB (pr1 x) (pr1 y)))
                            (pr1 (binprod_cone_pr1 q))
                            (pr1 (binprod_cone_pr2 q))))
    : disp_has_binprod (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    intros x y.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (Hcone x y ,, tt).
    - exact (tt ,, Hπ₁ x y).
    - exact (tt ,, Hπ₂ x y).
    - exact (λ z f g, tt ,, Hpair x y (make_binprod_cone z f g)).
  Defined.

  Definition subbicat_binprod
             (HB : has_binprod B)
             (HB' : is_univalent_2 B)
             (Hcone : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                      P₀ (pr1 (HB (pr1 x) (pr1 y))))
             (Hπ₁ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _
                      (Hcone x y)
                      (pr12 x)
                      (binprod_cone_pr1 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hπ₂ : ∏ (x y : subbicat P₀ P₁ Pid Pcomp),
                    P₁ _ _
                      (Hcone x y)
                      (pr12 y)
                      (binprod_cone_pr2 (pr1 (HB (pr1 x) (pr1 y)))))
             (Hpair : ∏ (x y : subbicat P₀ P₁ Pid Pcomp)
                        (q : binprod_cone x y),
                      P₁ _ _
                         (pr121 q)
                         (Hcone x y)
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
    - use (subbicat_disp_binprod HB Hcone).
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
                    P₁ _ _
                       (Hcone x y z f g)
                       (pr12 x)
                       (pb_cone_pr1 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (Hπ₂ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _
                       (Hcone x y z f g)
                       (pr12 y)
                       (pb_cone_pr2 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (H_ump_mor : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                            (f : x --> z)
                            (g : y --> z)
                            (q : pb_cone f g),
                          P₁ _ _
                            (pr121 q)
                            (Hcone x y z f g)
                            (pb_ump_mor
                               (pr2 (HB (pr1 x) (pr1 y) (pr1 z) (pr1 f) (pr1 g)))
                               (total_pb_cone_help_cone _ q)))
    : disp_has_pb (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    intros x y z f g.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (Hcone x y z f g ,, tt).
    - exact (tt ,, Hπ₁ x y z f g).
    - exact (tt ,, Hπ₂ x y z f g).
    - exact (λ q, tt ,, H_ump_mor x y z f g q).
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
                    P₁ _ _
                       (Hcone x y z f g)
                       (pr12 x)
                       (pb_cone_pr1 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (Hπ₂ : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                      (f : x --> z)
                      (g : y --> z),
                    P₁ _ _
                       (Hcone x y z f g)
                       (pr12 y)
                       (pb_cone_pr2 (pr1 (HB _ _ _ (pr1 f) (pr1 g)))))
             (H_ump_mor : ∏ (x y z : subbicat P₀ P₁ Pid Pcomp)
                            (f : x --> z)
                            (g : y --> z)
                            (q : pb_cone f g),
                          P₁ _ _
                            (pr121 q)
                            (Hcone x y z f g)
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
    - apply (subbicat_disp_has_pb HB Hcone).
      + exact Hπ₁.
      + exact Hπ₂.
      + exact H_ump_mor.
  Defined.

  (**
   4. Eilenberg-Moore objects
   *)
  Definition subbicat_disp_has_em
             (HB : bicat_has_em B)
             (Hcone : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp))),
                      P₀ (pr11 (HB (pr1_of_mnd_total_bicat m))))
             (Hmor : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp))),
                     P₁ _ _
                        (Hcone m)
                        (pr121 m)
                        (mor_of_mnd_mor
                           (mor_of_em_cone
                              _
                              (pr1 (HB (pr1_of_mnd_total_bicat m))))))
             (Hump : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp)))
                       (q : em_cone m),
                     P₁ _ _
                        (pr121 q)
                        (Hcone m)
                        (em_ump_1_mor
                           (pr1_of_mnd_total_bicat m)
                           (pr2 (HB (pr1_of_mnd_total_bicat m)))
                           (pr1_of_em_cone (disp_subbicat P₀ P₁ Pid Pcomp) m q)))
    : disp_has_em (disp_subbicat P₀ P₁ Pid Pcomp) HB.
  Proof.
    intro m.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (Hcone m ,, tt).
    - exact (tt ,, Hmor m).
    - exact (tt ,, tt).
    - exact (λ q, tt ,, Hump m q).
  Defined.

  Definition subbicat_has_em
             (HB : bicat_has_em B)
             (HB' : is_univalent_2 B)
             (Hcone : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp))),
                      P₀ (pr11 (HB (pr1_of_mnd_total_bicat m))))
             (Hmor : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp))),
                     P₁ _ _
                        (Hcone m)
                        (pr121 m)
                        (mor_of_mnd_mor
                           (mor_of_em_cone
                              _
                              (pr1 (HB (pr1_of_mnd_total_bicat m))))))
             (Hump : ∏ (m : mnd (total_bicat (disp_subbicat P₀ P₁ Pid Pcomp)))
                       (q : em_cone m),
                     P₁ _ _
                        (pr121 q)
                        (Hcone m)
                        (em_ump_1_mor
                           (pr1_of_mnd_total_bicat m)
                           (pr2 (HB (pr1_of_mnd_total_bicat m)))
                           (pr1_of_em_cone (disp_subbicat P₀ P₁ Pid Pcomp) m q)))
    : bicat_has_em (subbicat P₀ P₁ Pid Pcomp).
  Proof.
    use total_bicat_has_em.
    - apply disp_2cells_isaprop_subbicat.
    - intros.
      apply subbicat_disp_2cell_over.
    - use disp_locally_groupoid_subbicat.
      exact HB'.
    - exact HB.
    - apply (subbicat_disp_has_em HB Hcone).
      + exact Hmor.
      + exact Hump.
  Defined.
End LimitsSubbicat.
