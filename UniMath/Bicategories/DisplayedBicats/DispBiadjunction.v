(* ------------------------------------------------------------------------- *)
(** Displayed biadjunction.

   Contents:
   - Definition of displayed biadjunction.
   - Associated total biadjunction.
                                                                             *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
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
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.

Import PseudoFunctor.Notations.

Local Open Scope cat.

Section DisplayedBiadjunction.

Context {B₁ B₂ : bicat}
        (D₁ : disp_bicat B₁)
        (D₂ : disp_bicat B₂).

Definition disp_left_biadj_unit_counit
           {L : psfunctor B₁ B₂}
           (e : left_biadj_unit_counit L)
           (LL : disp_psfunctor D₁ D₂ L)
  : UU
  := ∑ (RR : disp_psfunctor D₂ D₁ e),
     disp_pstrans
       (disp_pseudo_id D₁)
       (disp_pseudo_comp _ _ _ _ _ LL RR)
       (biadj_unit e)
     ×
     disp_pstrans
       (disp_pseudo_comp _ _ _ _ _ RR LL)
       (disp_pseudo_id D₂)
       (biadj_counit e).

Definition right_adj_of_disp_left_biadj
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
  : disp_psfunctor D₂ D₁ e
  := pr1 ee.

Definition unit_of_disp_left_biadj
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
  : disp_pstrans
      (disp_pseudo_id D₁)
      (disp_pseudo_comp _ _ _ _ _ LL (right_adj_of_disp_left_biadj ee))
      (biadj_unit e)
  := pr12 ee.

Definition counit_of_disp_left_biadj
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ (right_adj_of_disp_left_biadj ee) LL)
      (disp_pseudo_id D₂)
      (biadj_counit e)
  := pr22 ee.

Definition total_left_biadj_unit_counit
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
  : left_biadj_unit_counit (total_psfunctor _ _ _ LL).
Proof.
  use make_biadj_unit_counit.
  - exact (total_psfunctor _ _ _ (right_adj_of_disp_left_biadj ee)).
  - apply pstrans_on_data_to_pstrans.
    pose (unit_of_disp_left_biadj ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    apply tuu.
  - apply pstrans_on_data_to_pstrans.
    pose (counit_of_disp_left_biadj ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    apply tuu.
Defined.

(** ** Triangles *)
Definition disp_left_biadj_left_triangle
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
           (e_lt : biadj_triangle_l_law e)
  : UU
  := disp_invmodification
       _ _ _ _
       (disp_comp_pstrans
          (disp_rinvunitor_pstrans LL)
          (disp_comp_pstrans
             (disp_left_whisker LL (unit_of_disp_left_biadj ee))
             (disp_comp_pstrans
                (disp_lassociator_pstrans _ _ _)
                (disp_comp_pstrans
                   (disp_right_whisker LL (counit_of_disp_left_biadj ee))
                   (disp_lunitor_pstrans LL))
             )
          )
       )
       (disp_id_pstrans LL)
       e_lt.

Definition disp_left_biadj_right_triangle
           {L : psfunctor B₁ B₂}
           {e : left_biadj_unit_counit L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_unit_counit e LL)
           (e_lt : biadj_triangle_r_law e)
  : UU
  := let RR := right_adj_of_disp_left_biadj ee in
     disp_invmodification
       _ _ _ _
       (disp_comp_pstrans
          (disp_pstrans_linvunitor RR)
          (disp_comp_pstrans
             (disp_right_whisker RR (unit_of_disp_left_biadj ee))
             (disp_comp_pstrans
                (disp_pstrans_rassociator _ _ _)
                (disp_comp_pstrans
                   (disp_left_whisker RR (counit_of_disp_left_biadj ee))
                   (disp_runitor_pstrans RR))
             )
          )
       )
       (disp_id_pstrans RR)
       e_lt.

(** ** Data *)
Definition disp_left_biadj_data
           {L : psfunctor B₁ B₂}
           (e : left_biadj_data L)
           (LL : disp_psfunctor D₁ D₂ L)
  : UU
  := ∑ (ee : disp_left_biadj_unit_counit e LL),
     (disp_left_biadj_left_triangle ee (pr12 e))
       ×
       disp_left_biadj_right_triangle ee (pr22 e).

(** ** Total biadjunction. *)
Definition total_left_biadj_data
           {L : psfunctor B₁ B₂}
           {e : left_biadj_data L}
           {LL : disp_psfunctor D₁ D₂ L}
           (ee : disp_left_biadj_data e LL)
  : left_biadj_data (total_psfunctor _ _ _ LL).
Proof.
  use make_biadj_data.
  - exact (total_left_biadj_unit_counit (pr1 ee)).
  - pose (total_invmodification _ _ _ _ _ _ _ (pr12 ee)) as m.
    unfold biadj_triangle_l_law.
    apply make_invertible_modification_on_data.
    use tpair.
    + intro X.
      exact (invertible_modcomponent_of m X).
    + exact (modnaturality_of (pr1 m)).
  - pose (total_invmodification _ _ _ _ _ _ _ (pr22 ee)) as m.
    unfold biadj_triangle_r_law.
    apply make_invertible_modification_on_data.
    use tpair.
    + intro X.
      exact (invertible_modcomponent_of m X).
    + exact (modnaturality_of (pr1 m)).
Defined.
End DisplayedBiadjunction.
