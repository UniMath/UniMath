(* ******************************************************************************* *)
(** * Yoneda embedding
    Niccolò Veltri, Niels van der Weide
    April 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Representable.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.


Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Yoneda.

Context {C : bicat}.
Variable (C_is_univalent_2_1 : is_univalent_2_1 C).


Definition representable_id_inv2cell (X : C)
  : invertible_modification_data (id_pstrans (representable C_is_univalent_2_1 X))
                                 (representable1 C_is_univalent_2_1 (id₁ X)).
Proof.
  intro Y.
  use make_invertible_2cell.
  - use make_nat_trans.
    * intro f.
      cbn in *.
      apply rinvunitor.
    * abstract
        (intros f g η ;
         cbn in * ;
         rewrite rwhisker_hcomp ;
         apply rinvunitor_natural).
  - use make_is_invertible_2cell.
    + use make_nat_trans.
      * intro f.
        cbn in *.
        apply runitor.
      * abstract (intros f g η ; cbn ; apply vcomp_runitor).
    + use nat_trans_eq.
      { exact (pr2 C Y X). }
      abstract (intro f ;
                cbn in * ;
                apply rinvunitor_runitor).
    + use nat_trans_eq.
      { exact (pr2 C Y X). }
      abstract (intro f ;
                cbn in * ;
                apply runitor_rinvunitor).
Defined.

Definition representable_id_is_mod (X : C)
  : is_modification (representable_id_inv2cell X).
Proof.
  intros Y Z f.
  use nat_trans_eq.
  { exact (pr2 C Z X). }
  intro g.
  cbn in *.
  repeat (rewrite id2_left).
  symmetry.
  apply rinvunitor_triangle.
Qed.


Definition representable_id_invmod (X : C)
  : invertible_modification (id_pstrans _) (representable1 C_is_univalent_2_1 (id₁ X)).
Proof.
  use make_invertible_modification.
  - exact (representable_id_inv2cell X).
  - exact (representable_id_is_mod X).
Defined.

Definition representable_comp_inv2cell {X Y Z: C} (f : X --> Y) (g : Y --> Z)
  : invertible_modification_data
      (comp_pstrans (representable1 C_is_univalent_2_1 f)
                  (representable1 C_is_univalent_2_1 g))
      (representable1 C_is_univalent_2_1 (f · g)).
Proof.
  intro W.
  use make_invertible_2cell.
  - use make_nat_trans.
    + intro h.
      cbn in *.
      apply rassociator.
    + abstract (intros V U h;
                cbn in *;
                apply rwhisker_rwhisker_alt).
  - use make_is_invertible_2cell.
    + use make_nat_trans.
      * intro h.
        cbn in *.
        apply lassociator.
      * abstract (intros h k η;
                  cbn in *;
                  symmetry;
                  apply rwhisker_rwhisker).
    + use nat_trans_eq.
      { exact (pr2 C W Z). }
      abstract (intro h;
                cbn in *;
                apply rassociator_lassociator).
    + use nat_trans_eq.
      { exact (pr2 C W Z). }
      abstract (intro h;
                cbn in *;
                apply lassociator_rassociator).
Defined.

Definition representable_comp_is_mod {X Y Z: C} (f : X --> Y) (g : Y --> Z)
  : is_modification (representable_comp_inv2cell f g).
Proof.
  intros W V h.
  use nat_trans_eq.
  { exact (pr2 C V Z). }
  intros k.
  cbn in *.
  repeat (rewrite id2_left).
  repeat (rewrite id2_right).
  rewrite rwhisker_hcomp.
  rewrite <- vassocr.
  symmetry.
  rewrite lwhisker_hcomp.
  apply inverse_pentagon_5.
Qed.

Definition representable_comp_invmod {X Y Z: C} (f : X --> Y) (g : Y --> Z)
  : invertible_modification
      (comp_pstrans (representable1 C_is_univalent_2_1 f)
                  (representable1 C_is_univalent_2_1 g))
      (representable1 C_is_univalent_2_1 (f · g)).
Proof.
  use make_invertible_modification.
  - exact (representable_comp_inv2cell f g).
  - exact (representable_comp_is_mod f g).
Defined.

Definition y_data : psfunctor_data C (psfunctor_bicat (op1_bicat C) bicat_of_univ_cats).
Proof.
  use make_psfunctor_data.
  - exact (representable C_is_univalent_2_1).
  - intros X Y.
    exact (representable1 C_is_univalent_2_1).
  - intros X Y f g.
    exact (representable2 C_is_univalent_2_1).
  - intro X.
    apply (representable_id_invmod X).
  - intros X Y Z f g.
    apply (representable_comp_invmod f g).
Defined.

Definition y_laws : psfunctor_laws y_data.
Proof.
  repeat split; cbn.
  - intros X Y f.
    use modification_eq.
    intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro g.
    cbn in *.
    apply lwhisker_id2.
  - intros X Y f g h η φ.
    use modification_eq.
    intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro k.
    cbn in *.
    symmetry.
    apply lwhisker_vcomp.
  - intros X Y f.
    use modification_eq.
    intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro g.
    cbn in *.
    symmetry.
    rewrite <- vassocr.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    apply id2_rwhisker.
  - intros X Y f.
    use modification_eq.
    intro Z.
    use nat_trans_eq.
    { exact (pr2 C Z Y). }
    intro g.
    cbn in *.
    symmetry.
    rewrite <- vassocr.
     rewrite runitor_triangle.
    apply rinvunitor_runitor.
  - intros X Y Z W f g h.
    use modification_eq.
    intro V.
    use nat_trans_eq.
    { exact (pr2 C V W). }
    intro k.
    cbn in *.
    rewrite id2_left.
    symmetry.
    rewrite rwhisker_hcomp.
    rewrite inverse_pentagon_6.
    rewrite lwhisker_hcomp.
    apply vassocr.
  - intros X Y Z f g h η.
    use modification_eq.
    intro W.
    use nat_trans_eq.
    { exact (pr2 C W Z). }
    intro k.
    cbn in *.
    apply lwhisker_lwhisker_rassociator.
  - intros X Y Z f g h η.
    use modification_eq.
    intro W.
    use nat_trans_eq.
    { exact (pr2 C W Z). }
    intro k.
    cbn in *.
    apply rwhisker_lwhisker_rassociator.
Qed.

Definition y_invertible_cells : invertible_cells y_data.
Proof.
  split.
  - intro X.
    apply (representable_id_invmod X).
  - intros X Y Z f g.
    apply (representable_comp_invmod f g).
Defined.

Definition y : psfunctor C (psfunctor_bicat (op1_bicat C) bicat_of_univ_cats).
Proof.
  use make_psfunctor.
  - exact y_data.
  - exact y_laws.
  - exact y_invertible_cells.
Defined.

End Yoneda.
