(*********************************************************************

 Cleavings of bicategories

 In this file, we define cleaving of bicategories

 1. Cartesian pseudofunctors
 2. Cartesian pseudofunctors from global cleavings

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Cartesians.
Require Import UniMath.Bicategories.DisplayedBicats.EquivalenceBetweenCartesians.

Local Open Scope cat.
Local Open Scope mor_disp.

(** 1. Cartesian pseudofunctors *)
Definition global_cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f : b₁ --> b₂)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (Hff : cartesian_1cell D₁ ff),
     cartesian_1cell D₂ (disp_psfunctor_mor _ _ _ FF ff).

Definition local_cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f g : b₁ --> b₂)
       (α : f ==> g)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (gg : bb₁ -->[ g ] bb₂)
       (αα : ff ==>[ α ] gg)
       (Hαα : is_cartesian_2cell D₁ αα),
     is_cartesian_2cell D₂ (disp_psfunctor_cell _ _ _ FF αα).

Definition local_opcartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f g : b₁ --> b₂)
       (α : f ==> g)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (gg : bb₁ -->[ g ] bb₂)
       (αα : ff ==>[ α ] gg)
       (Hαα : is_opcartesian_2cell D₁ αα),
     is_opcartesian_2cell D₂ (disp_psfunctor_cell _ _ _ FF αα).

Definition cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := global_cartesian_disp_psfunctor FF × local_cartesian_disp_psfunctor FF.

(** Lmmas on cartesian pseudofunctors *)
Definition global_cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : global_cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? H.
  exact H.
Defined.

Definition global_cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : global_cartesian_disp_psfunctor FF)
           (HGG : global_cartesian_disp_psfunctor GG)
  : global_cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition local_cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : local_cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  exact H.
Defined.

Definition local_cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : local_cartesian_disp_psfunctor FF)
           (HGG : local_cartesian_disp_psfunctor GG)
  : local_cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition local_opcartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : local_opcartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  exact H.
Defined.

Definition local_opcartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : local_opcartesian_disp_psfunctor FF)
           (HGG : local_opcartesian_disp_psfunctor GG)
  : local_opcartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  split.
  - apply global_cartesian_id_psfunctor.
  - apply local_cartesian_id_psfunctor.
Defined.

Definition cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : cartesian_disp_psfunctor FF)
           (HGG : cartesian_disp_psfunctor GG)
  : cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  split.
  - apply global_cartesian_comp_psfunctor.
    + exact (pr1 HFF).
    + exact (pr1 HGG).
  - apply local_cartesian_comp_psfunctor.
    + exact (pr2 HFF).
    + exact (pr2 HGG).
Defined.

(**
 2. Cartesian pseudofunctors from global cleavings
 *)
Definition preserves_global_lifts
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (HD₁ : global_cleaving D₁)
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f : b₁ --> b₂)
       (bb₂ : D₁ b₂),
     cartesian_1cell
       D₂
       (disp_psfunctor_mor _ _ _ FF (pr12 (HD₁ b₁ b₂ bb₂ f))).

Definition preserves_global_lifts_to_cartesian
           {B : bicat}
           {D₁ : disp_bicat B}
           {D₂ : disp_bicat B}
           (HB : is_univalent_2 B)
           (HD₂ : disp_univalent_2 D₂)
           (HD₁ : global_cleaving D₁)
           {FF : disp_psfunctor D₁ D₂ (id_psfunctor _)}
           (HFF : preserves_global_lifts HD₁ FF)
  : global_cartesian_disp_psfunctor FF.
Proof.
  intros b₁ b₂ f bb₁ bb₂ ff Hff.
  refine (invertible_2cell_from_cartesian
            HB (pr2 HD₂)
            _
            (pr2 (disp_psfunctor_invertible_2cell
                    FF
                    (map_between_cartesian_1cell_commute
                       (pr2 HB)
                       ff
                       (pr22 (HD₁ b₁ b₂ bb₂ f)))))).
  use (invertible_2cell_from_cartesian
         HB (pr2 HD₂)
         _
         (pr2 (disp_psfunctor_comp _ _ _ _ _ _))).
  use (comp_cartesian_1cell HB).
  - exact (cartesian_1cell_disp_adj_equiv
             HB
             (pr1 HD₂)
             (@disp_psfunctor_id_on_disp_adjequiv
                _ _ _ FF
                _ _
                (_ ,, pr1 (disp_adj_equiv_between_cartesian_1cell
                             (pr2 HB)
                             Hff
                             (pr22 (HD₁ b₁ b₂ bb₂ f))))
                _ _ _
                (pr2 (disp_adj_equiv_between_cartesian_1cell
                        (pr2 HB)
                        Hff
                        (pr22 (HD₁ b₁ b₂ bb₂ f)))))).
  - apply HFF.
Defined.
