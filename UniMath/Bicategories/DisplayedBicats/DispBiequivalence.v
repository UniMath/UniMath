(* ------------------------------------------------------------------------- *)
(** Displayed biequivalence.

   Contents:
   - Definition of displayed biequivalence.
   - Associated total biequivalence.
                                                                             *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.

Import PseudoFunctor.Notations.

Local Open Scope cat.

Section DisplayedBiequivalence.

Context {B₁ B₂ : bicat}
        (D₁ : disp_bicat B₁)
        (D₂ : disp_bicat B₂).

Definition is_disp_biequivalence_unit_counit
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           (e : is_biequivalence_unit_counit F G)
           (FF : disp_psfunctor D₁ D₂ F) (GG : disp_psfunctor D₂ D₁ G)
  : UU
  := disp_pstrans (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                  (disp_pseudo_id D₁)
                  (unit_of_is_biequivalence e) ×
     disp_pstrans (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                  (disp_pseudo_id D₂)
                  (counit_of_is_biequivalence e).

Definition unit_of_is_disp_biequivalence
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : disp_pstrans (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                 (disp_pseudo_id D₁) (unit_of_is_biequivalence e)
  := pr1 ee.

Definition counit_of_is_disp_biequivalence
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : disp_pstrans (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                 (disp_pseudo_id D₂)
                 (counit_of_is_biequivalence e)
  := pr2 ee.

Definition total_is_biequivalence_unit_counit
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : is_biequivalence_unit_counit (total_psfunctor _ _ _ FF)
                                 (total_psfunctor _ _ _ GG).
Proof.
  split.
  - apply pstrans_on_data_to_pstrans.
    pose (unit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    apply tuu.
  - apply pstrans_on_data_to_pstrans.
    pose (counit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    apply tuu.
Defined.

(** ** Data *)
Definition disp_is_biequivalence_data
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           (a : is_biequivalence_adjoints e)
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : UU
  := ∑ (uu : disp_pstrans (disp_pseudo_id D₁)
                          (disp_pseudo_comp _ _ _ _ _ FF GG)
                          (invunit_of_is_biequivalence a))
       (cc : disp_pstrans (disp_pseudo_id D₂)
                              (disp_pseudo_comp _ _ _ _ _ GG FF)
                              (invcounit_of_is_biequivalence a)),
     (disp_invmodification _ _ _ _
                           (disp_comp_pstrans
                                         uu
                                         (unit_of_is_disp_biequivalence ee))
                           (disp_id_pstrans _)
                           (unitcounit_of_is_biequivalence _) ×
      disp_invmodification _ _ _ _
                           (disp_comp_pstrans
                                         (unit_of_is_disp_biequivalence ee)
                                         uu)
                           (disp_id_pstrans _)
                           (unitunit_of_is_biequivalence _)) ×
     (disp_invmodification _ _ _ _
                           (disp_comp_pstrans
                                         cc
                                         (counit_of_is_disp_biequivalence ee))
                           (disp_id_pstrans _)
                           (counitcounit_of_is_biequivalence _) ×
      disp_invmodification _ _ _ _
                           (disp_comp_pstrans
                                         (counit_of_is_disp_biequivalence ee)
                                         cc)
                           (disp_id_pstrans _)
                           (counitunit_of_is_biequivalence _)).

(** ** Total biequivalence. *)

Section total_biequivalence.

Context {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
        {e : is_biequivalence_unit_counit F G}
        (a : is_biequivalence_adjoints e)
        {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
        {ee : is_disp_biequivalence_unit_counit e FF GG}
        (aa : disp_is_biequivalence_data a ee).

Definition total_biequivalence_unit_inv
  : pstrans (id_psfunctor (total_bicat D₁))
            (comp_psfunctor (total_psfunctor D₂ D₁ G GG) (total_psfunctor D₁ D₂ F FF)).
Proof.
  apply pstrans_on_data_to_pstrans.
  pose (pr1 aa) as aapr.
  pose (total_pstrans _ _ _ aapr) as taapr.
  apply taapr.
Defined.

Definition total_biequivalence_counit_inv
  : pstrans (id_psfunctor (total_bicat D₂))
            (comp_psfunctor (total_psfunctor D₁ D₂ F FF) (total_psfunctor D₂ D₁ G GG)).
Proof.
  apply pstrans_on_data_to_pstrans.
  pose (pr12 aa) as aapr.
  pose (total_pstrans _ _ _ aapr) as taapr.
  apply taapr.
Defined.

Opaque comp_psfunctor.

Definition total_biequivalence_unit_unit_inv
  : invertible_modification
      (comp_pstrans
         (unit_of_is_biequivalence (total_is_biequivalence_unit_counit ee))
         total_biequivalence_unit_inv)
      (id_pstrans (comp_psfunctor (total_psfunctor D₂ D₁ G GG)
                         (total_psfunctor D₁ D₂ F FF))).
Proof.
  pose (total_invmodification _ _ _ _ _ _ _ (pr21 (pr22 aa))) as m.
  apply make_invertible_modification_on_data.
  use tpair.
  - intro X.
    exact (invertible_modcomponent_of m X).
  - exact (modnaturality_of (pr1 m)).
Defined.

Definition total_biequivalence_unit_inv_unit
  : invertible_modification
      (comp_pstrans
         total_biequivalence_unit_inv
         (unit_of_is_biequivalence (total_is_biequivalence_unit_counit ee)))
      (id_pstrans (id_psfunctor (total_bicat D₁))).
Proof.
  pose (total_invmodification _ _ _ _ _ _ _ (pr11 (pr22 aa))) as m.
  apply make_invertible_modification_on_data.
  use tpair.
  - intro X.
    exact (invertible_modcomponent_of m X).
  - exact (modnaturality_of (pr1 m)).
Defined.

Definition total_biequivalence_counit_counit_inv
  : invertible_modification
      (comp_pstrans
         (counit_of_is_biequivalence (total_is_biequivalence_unit_counit ee))
         total_biequivalence_counit_inv)
    (id_pstrans (comp_psfunctor (total_psfunctor D₁ D₂ F FF) (total_psfunctor D₂ D₁ G GG))).
Proof.
  pose (total_invmodification _ _ _ _ _ _ _ (pr22 (pr22 aa))) as m.
  apply make_invertible_modification_on_data.
  use tpair.
  - intro X.
    exact (invertible_modcomponent_of m X).
  - exact (modnaturality_of (pr1 m)).
Defined.

Definition total_biequivalence_counit_inv_counit
  : invertible_modification
      (comp_pstrans
         total_biequivalence_counit_inv
         (counit_of_is_biequivalence (total_is_biequivalence_unit_counit ee)))
      (id_pstrans (id_psfunctor (total_bicat D₂))).
Proof.
  pose (total_invmodification _ _ _ _ _ _ _ (pr12 (pr22 aa))) as m.
  apply make_invertible_modification_on_data.
  use tpair.
  - intro X.
    exact (invertible_modcomponent_of m X).
  - exact (modnaturality_of (pr1 m)).
Defined.

Definition total_is_biequivalence
  : is_biequivalence (total_psfunctor _ _ _ FF).
Proof.
  use make_is_biequivalence_from_unit_counit.
  - exact (total_psfunctor _ _ _ GG).
  - exact (total_is_biequivalence_unit_counit ee).
  - exact total_biequivalence_unit_inv.
  - exact total_biequivalence_counit_inv.
  - exact total_biequivalence_unit_unit_inv.
  - exact total_biequivalence_unit_inv_unit.
  - exact total_biequivalence_counit_counit_inv.
  - exact total_biequivalence_counit_inv_counit.
Defined.

End total_biequivalence.
End DisplayedBiequivalence.
