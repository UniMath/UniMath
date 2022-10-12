(********************************************************************

 Limits in some standard constructions

 Contents
 1. Limits in the full subbicategory
 2. Limits in the product of displayed bicategories

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
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

(**
 1. Limits in the full subbicategory
 *)
Section LimitsFullSubbicat.
  Context {B : bicat}
          (P : B → UU).

  Definition disp_fullsubbicat_bifinal
             (HB : bifinal_obj B)
             (H : P (pr1 HB))
    : disp_bifinal_obj (disp_fullsubbicat _ P) HB
    := H ,, λ _ _, tt.

  Definition disp_fullsubbicat_binprod
             (HB : has_binprod B)
             (H : ∏ (x y : B)
                    (Hx : P x)
                    (Hy : P y),
                  P (pr1 (HB x y)))
    : disp_has_binprod (disp_fullsubbicat _ P) HB
    := λ x y, H _ _ (pr2 x) (pr2 y) ,, tt ,, tt ,, λ _ _ _, tt.

  Definition disp_fullsubbicat_has_pb
             (HB : has_pb B)
             (H : ∏ (x y z : B)
                    (f : x --> z)
                    (g : y --> z)
                    (Hx : P x)
                    (Hy : P y)
                    (Hz : P z),
                  P (pr1 (HB x y z f g)))
    : disp_has_pb (disp_fullsubbicat _ P) HB
    := λ x y z f g,
       H _ _ _ _ _ (pr2 x) (pr2 y) (pr2 z) ,, tt ,, tt ,, λ _, tt.

  Definition disp_fullsubbicat_em_obj
             (HB : bicat_has_em B)
             (H : ∏ (m : mnd (total_bicat (disp_fullsubbicat _ P))),
                  P (pr11 (HB (pr1_of_mnd_total_bicat m))))
    : disp_has_em (disp_fullsubbicat _ P) HB
    := λ m, H m ,, tt ,, tt ,, λ _, tt.
End LimitsFullSubbicat.

(**
 2. Limits in the product of displayed bicategories
 *)
Definition disp_dirprod_bifinal
           {B : bicat}
           (HB : bifinal_obj B)
           (D₁ D₂ : disp_bicat B)
           (HD₁ : disp_bifinal_obj D₁ HB)
           (HD₂ : disp_bifinal_obj D₂ HB)
  : disp_bifinal_obj (disp_dirprod_bicat D₁ D₂) HB.
Proof.
  refine ((pr1 HD₁ ,, pr1 HD₂) ,, λ x xx, (_ ,, _)) ; cbn.
  - exact (pr2 HD₁ x (pr1 xx)).
  - exact (pr2 HD₂ x (pr2 xx)).
Defined.

Definition disp_dirprod_binprod
           {B : bicat}
           (HB : has_binprod B)
           (D₁ D₂ : disp_bicat B)
           (HD₁ : disp_has_binprod D₁ HB)
           (HD₂ : disp_has_binprod D₂ HB)
  : disp_has_binprod (disp_dirprod_bicat D₁ D₂) HB.
Proof.
  simple refine (λ x y, _ ,, _ ,, _ ,, λ z f g, _).
  - simple refine (_ ,, _).
    + exact (pr1 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y))).
    + exact (pr1 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y))).
  - simple refine (_ ,, _).
    + exact (pr12 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y))).
    + exact (pr12 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y))).
  - simple refine (_ ,, _).
    + exact (pr122 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y))).
    + exact (pr122 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y))).
  - simple refine (_ ,, _).
    + exact (pr222 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y))
                        (pr1 z ,, pr12 z) (pr1 f ,, pr12 f) (pr1 g ,, pr12 g)).
    + exact (pr222 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y))
                        (pr1 z ,, pr22 z) (pr1 f ,, pr22 f) (pr1 g ,, pr22 g)).
Defined.

Definition disp_dirprod_pb
           {B : bicat}
           (HB : has_pb B)
           (D₁ D₂ : disp_bicat B)
           (HD₁ : disp_has_pb D₁ HB)
           (HD₂ : disp_has_pb D₂ HB)
  : disp_has_pb (disp_dirprod_bicat D₁ D₂) HB.
Proof.
  simple refine (λ x y z f g, _ ,, _ ,, _ ,, λ q, _).
  - simple refine (_ ,, _).
    + exact (pr1 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y) (pr1 z ,, pr12 z)
                      (pr1 f ,, pr12 f) (pr1 g ,, pr12 g))).
    + exact (pr1 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y) (pr1 z ,, pr22 z)
                      (pr1 f ,, pr22 f) (pr1 g ,, pr22 g))).
  - simple refine (_ ,, _).
    + exact (pr12 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y) (pr1 z ,, pr12 z)
                       (pr1 f ,, pr12 f) (pr1 g ,, pr12 g))).
    + exact (pr12 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y) (pr1 z ,, pr22 z)
                       (pr1 f ,, pr22 f) (pr1 g ,, pr22 g))).
  - simple refine (_ ,, _).
    + exact (pr122 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y) (pr1 z ,, pr12 z)
                        (pr1 f ,, pr12 f) (pr1 g ,, pr12 g))).
    + exact (pr122 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y) (pr1 z ,, pr22 z)
                        (pr1 f ,, pr22 f) (pr1 g ,, pr22 g))).
  - simple refine (_ ,, _).
    + pose (q' := @make_pb_cone
                    (total_bicat D₁)
                    (pr1 x ,, pr12 x) (pr1 y ,, pr12 y) (pr1 z ,, pr12 z)
                    (pr1 f,, pr12 f) (pr1 g,, pr12 g)
                    (pr1 (pb_cone_obj q) ,, pr12 (pb_cone_obj q))
                    (pr1 (pb_cone_pr1 q) ,, pr12 (pb_cone_pr1 q))
                    (pr1 (pb_cone_pr2 q) ,, pr12 (pb_cone_pr2 q))
                    (pr1_dirprod_invertible_2cell _ _ (pb_cone_cell q))).
      pose (m := pr222 (HD₁ (pr1 x ,, pr12 x) (pr1 y ,, pr12 y) (pr1 z ,, pr12 z)
                            (pr1 f ,, pr12 f) (pr1 g ,, pr12 g)) q').
      cbn in m ; cbn.
      use (transportf
             (λ w,
              _
              -->[ pb_ump_mor _ (make_pb_cone _ _ _ w) ]
              pr1
                (HD₁
                   (pr1 x,, pr12 x)
                   (pr1 y,, pr12 y)
                   (pr1 z,, pr12 z)
                   (pr1 f,, pr12 f)
                   (pr1 g,, pr12 g)))
             _
             m).
      abstract
        (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
    + pose (q' := @make_pb_cone
                    (total_bicat D₂)
                    (pr1 x ,, pr22 x) (pr1 y ,, pr22 y) (pr1 z ,, pr22 z)
                    (pr1 f,, pr22 f) (pr1 g,, pr22 g)
                    (pr1 (pb_cone_obj q) ,, pr22 (pb_cone_obj q))
                    (pr1 (pb_cone_pr1 q) ,, pr22 (pb_cone_pr1 q))
                    (pr1 (pb_cone_pr2 q) ,, pr22 (pb_cone_pr2 q))
                    (pr2_dirprod_invertible_2cell _ _ (pb_cone_cell q))).
      pose (m := pr222 (HD₂ (pr1 x ,, pr22 x) (pr1 y ,, pr22 y) (pr1 z ,, pr22 z)
                            (pr1 f ,, pr22 f) (pr1 g ,, pr22 g)) q').
      cbn in m ; cbn.
      use (transportf
             (λ w,
              _
              -->[ pb_ump_mor _ (make_pb_cone _ _ _ w) ]
              pr1
                (HD₂
                   (pr1 x,, pr22 x)
                   (pr1 y,, pr22 y)
                   (pr1 z,, pr22 z)
                   (pr1 f,, pr22 f)
                   (pr1 g,, pr22 g)))
             _
             m).
      abstract
        (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
Defined.
