(* ------------------------------------------------------------------------- *)
(** Displayed biequivalence.                                                 *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.

Import PseudoFunctor.Notations.

Local Open Scope cat.

Opaque ps_comp.

Definition TODO {A : UU} : A.
Admitted.

Definition is_psfunctor_eq_to_pstrans
           {B₁ B₂ : bicat}
           (F : psfunctor_data B₁ B₂)
           (HF₁ HF₂ : is_psfunctor F)
  : pstrans (F,,HF₁) (F,,HF₂).
Proof.
  use make_pstrans.
  - use make_pstrans_data.
    + intros x.
      exact (id₁ _).
    + intros x y f. cbn.
      use make_invertible_2cell.
      * exact (lunitor _ • rinvunitor _).
      * is_iso.
  - apply TODO.
Defined.

Section DisplayedBiequivalece.

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
  - pose (unit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    refine (comp_trans _ (comp_trans tuu _)).
    + apply is_psfunctor_eq_to_pstrans.
    + apply is_psfunctor_eq_to_pstrans.
  - pose (counit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    refine (comp_trans _ (comp_trans tuu _)).
    + apply is_psfunctor_eq_to_pstrans.
    + apply is_psfunctor_eq_to_pstrans.
Defined.

End DisplayedBiequivalece.