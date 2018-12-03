(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Various basic constructions of displayed and non displayed bicategories:
 - Unit displayed bicategory of a displayed 1-category.
 - Full subbicategory of a bicategory.
 - Direct product of bicategories.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* ----------------------------------------------------------------------------------- *)
(** Full sub-bicategory associated to a bicategory and a predicate on objects          *)
(* ----------------------------------------------------------------------------------- *)

Section Disp_Prebicat_Cells_Unit.

  Context {C : bicat} (D : disp_cat_data C).

  Definition disp_prebicat_cells_unit
    : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists D. red. intros. exact unit.
  Defined.

  Definition disp_prebicat_cells_unit_ops
    : disp_prebicat_ops disp_prebicat_cells_unit.
  Proof.
    repeat use tpair; cbn; intros; exact tt.
  Defined.

  Definition disp_prebicat_cells_unit_data : disp_prebicat_data C
    := _ ,, disp_prebicat_cells_unit_ops.

  Lemma disp_prebicat_cells_unit_laws
    : disp_prebicat_laws disp_prebicat_cells_unit_data.
  Proof.
    repeat use tpair; red; intros; apply (proofirrelevance _ isapropunit).
  Qed.

  Definition disp_cell_unit_prebicat : disp_prebicat C
    := _ ,, disp_prebicat_cells_unit_laws.
End Disp_Prebicat_Cells_Unit.

Section FullSubBicat.
  Variable (C : bicat)
           (P : C → UU).

  Definition disp_fullsubprebicat : disp_prebicat C
    := disp_cell_unit_prebicat (disp_full_sub_data C P).

  Definition disp_fullsubbicat : disp_bicat C.
  Proof.
    exists disp_fullsubprebicat.
    red. cbn. intros. exact isasetunit.
  Defined.

  Definition fullsubbicat : bicat := total_bicat disp_fullsubbicat.

  Definition mor_of_fullsub
             {X Y : fullsubbicat}
             (f : C⟦pr1 X, pr1 Y⟧)
    : X --> Y
    := (f ,, tt).

  Definition cell_of_fullsub
             {X Y : fullsubbicat}
             {f g : X --> Y}
             (α : pr1 f ==> pr1 g)
    : f ==> g
    := (α ,, tt).

  Definition disp_fullsubbicat_locally_univalent
    : disp_locally_univalent disp_fullsubbicat.
  Proof.
    apply fiberwise_local_univalent_is_locally_univalent.
    intros x y f xx yy ff gg.
    use isweqimplimpl.
    - intros.
      induction ff, gg.
      reflexivity.
    - apply isasetaprop.
      exact isapropunit.
    - simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
      + exact isapropunit.
      + simpl.
        apply (@isaprop_is_disp_invertible_2cell C disp_fullsubbicat _ _ _ _
                                                 (id2_invertible_2cell f)).
  Defined.

  Definition is_univalent_2_1_fullsubbicat
             (HC : is_univalent_2_1 C)
    : is_univalent_2_1 fullsubbicat.
  Proof.
    apply total_is_locally_univalent.
    - exact HC.
    - exact disp_fullsubbicat_locally_univalent.
  Defined.

  Definition is_univalent_2_0_fullsubbicat
             (HC0 : is_univalent_2_0 C)
             (HC1 : is_univalent_2_1 C)
             (HP : ∏ (x : C), isaprop (P x))
    : is_univalent_2_0 fullsubbicat.
  Proof.
    apply total_is_univalent_2_0.
    - exact HC0.
    - intros x y p xx yy.
      induction p.
      use isweqimplimpl.
      + intros ; cbn in *.
        apply HP.
      + apply isasetaprop.
        apply HP.
      + simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
        * exact isapropunit.
        * apply isaprop_disp_left_adjoint_equivalence.
          ** apply HC1.
          ** exact disp_fullsubbicat_locally_univalent.
  Defined.
End FullSubBicat.