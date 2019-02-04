(* ----------------------------------------------------------------------------------- *)
(** Discrete displayed bicategories

    Given a displayed category on some bicategory, we construct a displayed bicategory
    from it. The 2-cells are from the unit type.                                       *)
(* ----------------------------------------------------------------------------------- *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
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

  Definition disp_cell_unit_bicat : disp_bicat C.
  Proof.
    refine (disp_cell_unit_prebicat ,, _).
    intros a b f g x aa bb ff gg.
    apply isasetunit.
  Defined.

  (** Local Univalence *)
  Definition disp_cell_unit_bicat_univalent_2_1
             (H : ∏ (a b : C)
                    (f : a --> b)
                    (aa : D a) (bb : D b),
                  isaprop (aa -->[ f] bb))
    : disp_univalent_2_1 disp_cell_unit_bicat.
  Proof.
    intros a b f g p aa bb ff gg.
    use isweqimplimpl.
    - unfold idfun.
      cbn in *.
      intros.
      apply H.
    - apply isasetaprop.
      exact (H a b g aa bb).
    - simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
      + exact isapropunit.
      + apply (@isaprop_is_disp_invertible_2cell C disp_cell_unit_bicat).
  Defined.

  (** Global Univalence *)
  Definition disp_cell_unit_bicat_is_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_cell_unit_bicat a}
             {bb : disp_cell_unit_bicat b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x xx.
  Proof.
    use tpair.
    - exact tt.
    - split ; apply isapropunit.
  Defined.

  Definition disp_cell_unit_bicat_left_adjoint_equivalence
             {a b : C}
             (f : adjoint_equivalence a b)
             {aa : disp_cell_unit_bicat a}
             {bb : disp_cell_unit_bicat b}
             (ff : aa -->[ f] bb)
    : bb -->[ left_adjoint_right_adjoint f] aa
      →
      disp_left_adjoint_equivalence f ff.
  Proof.
    intros gg.
    use tpair.
    - use tpair.
      + exact gg.
      + exact (tt ,, tt).
    - split ; split ; cbn.
      + apply isapropunit.
      + apply isapropunit.
      + exact (disp_cell_unit_bicat_is_disp_invertible_2cell
                  (left_adjoint_unit f ,, _)
                  tt).
      + exact (disp_cell_unit_bicat_is_disp_invertible_2cell
                 (left_adjoint_counit f ,, _)
                 tt).
  Defined.

  Definition disp_cell_unit_bicat_left_adjoint_equivalence_inv
             {a b : C}
             (f : adjoint_equivalence a b)
             {aa : disp_cell_unit_bicat a}
             {bb : disp_cell_unit_bicat b}
             (ff : aa -->[ f] bb)
    : disp_left_adjoint_equivalence f ff
      →
      bb -->[ left_adjoint_right_adjoint f] aa.
  Proof.
    intros H.
    apply H.
  Defined.

  Definition disp_cell_unit_bicat_disp_cellset : has_disp_cellset disp_cell_unit_bicat.
  Proof.
    intro ; intros.
    apply isasetunit.
  Defined.

  Definition disp_cell_unit_bicat_left_adjoint_equivalence_weq
             {a b : C}
             (f : adjoint_equivalence a b)
             {aa : disp_cell_unit_bicat a}
             {bb : disp_cell_unit_bicat b}
             (ff : aa -->[ f] bb)
    : (bb -->[ left_adjoint_right_adjoint f] aa)
        ≃
        disp_left_adjoint_equivalence f ff.
  Proof.
    refine (disp_cell_unit_bicat_left_adjoint_equivalence f ff ,, _).
    use isweq_iso.
    - exact (disp_cell_unit_bicat_left_adjoint_equivalence_inv f ff).
    - reflexivity.
    - intros y.
      use subtypeEquality.
      + intro.
        do 2 apply isapropdirprod.
        * apply disp_cell_unit_bicat_disp_cellset.
        * apply disp_cell_unit_bicat_disp_cellset.
        * apply isaprop_is_disp_invertible_2cell.
        * apply isaprop_is_disp_invertible_2cell.
      + cbn.
        unfold disp_cell_unit_bicat_left_adjoint_equivalence_inv.
        use total2_paths_b.
        * reflexivity.
        * use total2_paths_b ; apply isapropunit.
  Defined.

  Definition disp_cell_unit_bicat_adjoint_equivalent
             {a b : C}
             (f : adjoint_equivalence a b)
             (aa : disp_cell_unit_bicat a)
             (bb : disp_cell_unit_bicat b)
    : (aa -->[ f] bb × bb -->[ left_adjoint_right_adjoint f] aa)
        ≃
        disp_adjoint_equivalence f aa bb.
  Proof.
    use weqfibtototal ; cbn.
    intro.
    apply disp_cell_unit_bicat_left_adjoint_equivalence_weq.
  Defined.

  Definition disp_cell_unit_bicat_idtoiso
             {a b : C}
             (p : a = b)
             (aa : disp_cell_unit_bicat a)
             (bb : disp_cell_unit_bicat b)
    : transportf disp_cell_unit_bicat p aa = bb
      →
      (aa -->[ idtoiso_2_0 _ _ p ] bb)
        ×
        (bb -->[ left_adjoint_right_adjoint (idtoiso_2_0 _ _ p)] aa).
  Proof.
    induction p ; cbn ; unfold idfun.
    intros pp.
    induction pp ; cbn.
    split ; apply id_disp.
  Defined.

  Definition disp_cell_unit_bicat_univalent_2_0
             (HC : is_univalent_2_1 C)
             (HDP : ∏ (a b : C)
                     (f : a --> b)
                     (aa : D a) (bb : D b),
                   isaprop (aa -->[ f] bb))
             (Dset : ∏ (a : C), isaset (D a))
             (inv : ∏ (a : C) (aa bb : disp_cell_unit_bicat a),
                    (aa -->[ id₁ a ] bb × bb -->[ id₁ a ] aa)
                    →
                    aa = bb)
    : disp_univalent_2_0 disp_cell_unit_bicat.
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros a aa bb.
    use isweqimplimpl.
    - intro η ; cbn ; unfold idfun.
      apply inv.
      exact (invmap (disp_cell_unit_bicat_adjoint_equivalent
                       (idtoiso_2_0 a a (idpath a))
                       aa bb) η).
    - apply (Dset a).
    - apply (isofhlevelweqf 1 (disp_cell_unit_bicat_adjoint_equivalent _ _ _)).
      apply isapropdirprod ; apply HDP.
  Defined.
End Disp_Prebicat_Cells_Unit.