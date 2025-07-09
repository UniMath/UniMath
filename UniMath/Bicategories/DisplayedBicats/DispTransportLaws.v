(***************************************************************************************

 Transport laws for displayed bicategories

 This file is a collection of random transport laws for displayed bicategories.

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Local Open Scope cat.

Definition transportf_disp_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
           (p : f = g)
  : disp_invertible_2cell (idtoiso_2_1 _ _ p) ff (transportf _ p ff).
Proof.
  induction p.
  cbn.
  exact (disp_id2_invertible_2cell ff).
Defined.

Definition disp_psfunctor_mor_transportb
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
           {x y : B₁}
           {f g : x --> y}
           (p : f = g)
           {xx : D₁ x}
           {yy : D₁ y}
           (gg : xx -->[ g ] yy)
  : disp_psfunctor_mor
      _ _ _ FF
      (transportb (λ z, xx -->[ z ] yy) p gg)
    =
    transportb
      (λ z, _ -->[ z ] _)
      (maponpaths (#F) p)
      (disp_psfunctor_mor _ _ _ FF gg).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition transportf_prewhisker_1cell
           {B : bicat}
           {D : disp_bicat B}
           {x y z : B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {f₁ f₂ : x --> y}
           {g : y --> z}
           (p : f₁ = f₂)
           (ff : xx -->[ f₁ ] yy)
           (gg : yy -->[ g ] zz)
  : (transportf
       (λ z, xx -->[ z ] yy)
       p
       ff
     ;;
     gg
     =
     transportf
       (λ z, xx -->[ z ] zz)
       (maponpaths (λ z, z · _) p)
       (ff ;; gg))%mor_disp.
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Definition transportf_postwhisker_1cell
           {B : bicat}
           {D : disp_bicat B}
           {x y z : B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {f : x --> y}
           {g₁ g₂ : y --> z}
           (p : g₁ = g₂)
           (ff : xx -->[ f ] yy)
           (gg : yy -->[ g₁ ] zz)
  : (ff
     ;;
     transportf
       (λ z, yy -->[ z ] zz)
       p
       gg
     =
     transportf
       (λ z, xx -->[ z ] zz)
       (maponpaths (λ z, _ · z) p)
       (ff ;; gg))%mor_disp.
Proof.
  induction p ; cbn.
  apply idpath.
Defined.
