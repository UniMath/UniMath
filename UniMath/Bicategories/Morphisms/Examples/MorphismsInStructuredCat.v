(******************************************************************

 Morphisms in structured categories

 Contents
 1. Adjunctions of categories with a terminal object
 2. Adjunctions of categories with binary products
 3. Adjunctions of categories with pullbacks
 4. Adjunctions of categories with an initial object
 5. Adjunctions of categories with binary coproducts

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.

Local Open Scope cat.

(**
 1. Adjunctions of categories with a terminal object
 *)
Section DispAdjunctionTerminalObj.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (a : adjunction C₁ C₂)
          (CC₁ : disp_bicat_terminal_obj C₁)
          (CC₂ : disp_bicat_terminal_obj C₂).

  Definition isaprop_disp_adjunction_univ_cat_with_terminal_obj
    : isaprop (disp_adjunction a CC₁ CC₂).
  Proof.
    use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; simpl.
    - apply isapropdirprod.
      + apply isaprop_preserves_terminal.
      + apply isapropunit.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
        * simpl.
          apply isapropdirprod.
          ** apply isaprop_preserves_terminal.
          ** apply isapropunit.
        * apply isapropdirprod.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
      + apply isapropdirprod ; apply disp_bicat_terminal_obj.
  Qed.

  Section MakeDispAdj.
    Context (H : preserves_terminal (pr1 a)).

    Let F : CC₁ -->[ a ] CC₂ := H ,, tt.

    Local Definition disp_left_adjoint_data_univ_cat_with_terminal_obj
      : disp_left_adjoint_data a F.
    Proof.
      refine ((_ ,, tt) ,, ((tt ,, tt) ,, (tt ,, tt))).
      exact (right_adjoint_preserves_terminal _ (left_adjoint_to_is_left_adjoint a)).
    Defined.

    Local Definition disp_left_adjoint_axioms_univ_cat_with_terminal_obj
      : disp_left_adjoint_axioms a disp_left_adjoint_data_univ_cat_with_terminal_obj.
    Proof.
      split ; apply disp_2cells_isaprop_subbicat.
    Qed.

    Local Definition disp_left_adjoint_univ_cat_with_terminal_obj
      : disp_left_adjoint a F.
    Proof.
      simple refine (_ ,, _).
      - exact disp_left_adjoint_data_univ_cat_with_terminal_obj.
      - exact disp_left_adjoint_axioms_univ_cat_with_terminal_obj.
    Defined.

    Definition disp_adjunction_univ_cat_with_terminal_obj
      : disp_adjunction a CC₁ CC₂.
    Proof.
      simple refine (_ ,, _).
      - exact F.
      - exact disp_left_adjoint_univ_cat_with_terminal_obj.
    Defined.
  End MakeDispAdj.

  Definition disp_adj_weq_preserves_terminal
    : disp_adjunction a CC₁ CC₂ ≃ preserves_terminal (pr1 a).
  Proof.
    use weqimplimpl.
    - intro aa.
      apply aa.
    - exact disp_adjunction_univ_cat_with_terminal_obj.
    - apply isaprop_disp_adjunction_univ_cat_with_terminal_obj.
    - apply isaprop_preserves_terminal.
  Defined.
End DispAdjunctionTerminalObj.

(**
 2. Adjunctions of categories with binary products
 *)
Section DispAdjunctionBinproduct.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (a : adjunction C₁ C₂)
          (CC₁ : disp_bicat_binprod C₁)
          (CC₂ : disp_bicat_binprod C₂).

  Definition isaprop_disp_adjunction_univ_cat_with_binprod
    : isaprop (disp_adjunction a CC₁ CC₂).
  Proof.
    use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; simpl.
    - apply isapropdirprod.
      + apply isaprop_preserves_binproduct.
      + apply isapropunit.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
        * simpl.
          apply isapropdirprod.
          ** apply isaprop_preserves_binproduct.
          ** apply isapropunit.
        * apply isapropdirprod.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
      + apply isapropdirprod ; apply disp_bicat_binprod.
  Qed.

  Section MakeDispAdj.
    Context (H : preserves_binproduct (pr1 a)).

    Let F : CC₁ -->[ a ] CC₂ := H ,, tt.

    Local Definition disp_left_adjoint_data_univ_cat_with_binprod
      : disp_left_adjoint_data a F.
    Proof.
      refine ((_ ,, tt) ,, ((tt ,, tt) ,, (tt ,, tt))).
      exact (right_adjoint_preserves_binproduct _ (left_adjoint_to_is_left_adjoint a)).
    Defined.

    Local Definition disp_left_adjoint_axioms_univ_cat_with_binprod
      : disp_left_adjoint_axioms a disp_left_adjoint_data_univ_cat_with_binprod.
    Proof.
      split ; apply disp_2cells_isaprop_subbicat.
    Qed.

    Local Definition disp_left_adjoint_univ_cat_with_binprod
      : disp_left_adjoint a F.
    Proof.
      simple refine (_ ,, _).
      - exact disp_left_adjoint_data_univ_cat_with_binprod.
      - exact disp_left_adjoint_axioms_univ_cat_with_binprod.
    Defined.

    Definition disp_adjunction_univ_cat_with_binprod
      : disp_adjunction a CC₁ CC₂.
    Proof.
      simple refine (_ ,, _).
      - exact F.
      - exact disp_left_adjoint_univ_cat_with_binprod.
    Defined.
  End MakeDispAdj.

  Definition disp_adj_weq_preserves_binprod
    : disp_adjunction a CC₁ CC₂ ≃ preserves_binproduct (pr1 a).
  Proof.
    use weqimplimpl.
    - intro aa.
      apply aa.
    - exact disp_adjunction_univ_cat_with_binprod.
    - apply isaprop_disp_adjunction_univ_cat_with_binprod.
    - apply isaprop_preserves_binproduct.
  Defined.
End DispAdjunctionBinproduct.

(**
 3. Adjunctions of categories with pullbacks
 *)
Section DispAdjunctionPullback.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (a : adjunction C₁ C₂)
          (CC₁ : disp_bicat_pullback C₁)
          (CC₂ : disp_bicat_pullback C₂).

  Definition isaprop_disp_adjunction_univ_cat_with_pb
    : isaprop (disp_adjunction a CC₁ CC₂).
  Proof.
    use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; simpl.
    - apply isapropdirprod.
      + apply isaprop_preserves_pullback.
      + apply isapropunit.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
        * simpl.
          apply isapropdirprod.
          ** apply isaprop_preserves_pullback.
          ** apply isapropunit.
        * apply isapropdirprod.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
      + apply isapropdirprod ; apply disp_bicat_pullback.
  Qed.

  Section MakeDispAdj.
    Context (H : preserves_pullback (pr1 a)).

    Let F : CC₁ -->[ a ] CC₂ := H ,, tt.

    Local Definition disp_left_adjoint_data_univ_cat_with_pb
      : disp_left_adjoint_data a F.
    Proof.
      refine ((_ ,, tt) ,, ((tt ,, tt) ,, (tt ,, tt))).
      exact (right_adjoint_preserves_pullback _ (left_adjoint_to_is_left_adjoint a)).
    Defined.

    Local Definition disp_left_adjoint_axioms_univ_cat_with_pb
      : disp_left_adjoint_axioms a disp_left_adjoint_data_univ_cat_with_pb.
    Proof.
      split ; apply disp_2cells_isaprop_subbicat.
    Qed.

    Local Definition disp_left_adjoint_univ_cat_with_pb
      : disp_left_adjoint a F.
    Proof.
      simple refine (_ ,, _).
      - exact disp_left_adjoint_data_univ_cat_with_pb.
      - exact disp_left_adjoint_axioms_univ_cat_with_pb.
    Defined.

    Definition disp_adjunction_univ_cat_with_pb
      : disp_adjunction a CC₁ CC₂.
    Proof.
      simple refine (_ ,, _).
      - exact F.
      - exact disp_left_adjoint_univ_cat_with_pb.
    Defined.
  End MakeDispAdj.

  Definition disp_adj_weq_preserves_pb
    : disp_adjunction a CC₁ CC₂ ≃ preserves_pullback (pr1 a).
  Proof.
    use weqimplimpl.
    - intro aa.
      apply aa.
    - exact disp_adjunction_univ_cat_with_pb.
    - apply isaprop_disp_adjunction_univ_cat_with_pb.
    - apply isaprop_preserves_pullback.
  Defined.
End DispAdjunctionPullback.

(**
 4. Adjunctions of categories with an initial object
 *)
Section DispAdjunctionInitial.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (a : adjunction C₁ C₂)
          (CC₁ : disp_bicat_initial_obj C₁)
          (CC₂ : disp_bicat_initial_obj C₂).

  Definition isaprop_disp_adjunction_univ_cat_with_initial
    : isaprop (disp_adjunction a CC₁ CC₂).
  Proof.
    use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; simpl.
    - apply isapropdirprod.
      + apply isaprop_preserves_initial.
      + apply isapropunit.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
        * simpl.
          apply isapropdirprod.
          ** apply isaprop_preserves_initial.
          ** apply isapropunit.
        * apply isapropdirprod.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
      + apply isapropdirprod ; apply disp_bicat_initial_obj.
  Qed.

  Section MakeDispAdj.
    Context (H : preserves_initial (pr112 a)).

    Local Definition disp_left_adjoint_univ_cat_with_initial_1cell
      : CC₁ -->[ a ] CC₂.
    Proof.
      refine (_ ,, tt).
      exact (left_adjoint_preserves_initial _ (left_adjoint_to_is_left_adjoint a)).
    Defined.

    Let F := disp_left_adjoint_univ_cat_with_initial_1cell.

    Local Definition disp_left_adjoint_data_univ_cat_with_initial
      : disp_left_adjoint_data a F.
    Proof.
      refine ((H ,, tt) ,, ((tt ,, tt) ,, (tt ,, tt))).
    Defined.

    Local Definition disp_left_adjoint_axioms_univ_cat_with_initial
      : disp_left_adjoint_axioms a disp_left_adjoint_data_univ_cat_with_initial.
    Proof.
      split ; apply disp_2cells_isaprop_subbicat.
    Qed.

    Local Definition disp_left_adjoint_univ_cat_with_initial
      : disp_left_adjoint a F.
    Proof.
      simple refine (_ ,, _).
      - exact disp_left_adjoint_data_univ_cat_with_initial.
      - exact disp_left_adjoint_axioms_univ_cat_with_initial.
    Defined.

    Definition disp_adjunction_univ_cat_with_initial
      : disp_adjunction a CC₁ CC₂.
    Proof.
      simple refine (_ ,, _).
      - exact F.
      - exact disp_left_adjoint_univ_cat_with_initial.
    Defined.
  End MakeDispAdj.

  Definition disp_adj_weq_preserves_initial
    : disp_adjunction a CC₁ CC₂ ≃ preserves_initial (pr112 a).
  Proof.
    use weqimplimpl.
    - intro aa.
      apply aa.
    - exact disp_adjunction_univ_cat_with_initial.
    - apply isaprop_disp_adjunction_univ_cat_with_initial.
    - apply isaprop_preserves_initial.
  Defined.
End DispAdjunctionInitial.

Print univ_cat_with_bincoprod.
(**
 5. Adjunctions of categories with binary coproducts
 *)
Section DispAdjunctionCoprod.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (a : adjunction C₁ C₂)
          (CC₁ : disp_bicat_bincoprod C₁)
          (CC₂ : disp_bicat_bincoprod C₂).

  Definition isaprop_disp_adjunction_univ_cat_with_bincoprod
    : isaprop (disp_adjunction a CC₁ CC₂).
  Proof.
    use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; simpl.
    - apply isapropdirprod.
      + apply isaprop_preserves_bincoproduct.
      + apply isapropunit.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
        * simpl.
          apply isapropdirprod.
          ** apply isaprop_preserves_bincoproduct.
          ** apply isapropunit.
        * apply isapropdirprod.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
          ** simpl ; apply isapropdirprod ; apply isapropunit.
      + apply isapropdirprod ; apply disp_bicat_bincoprod.
  Qed.

  Section MakeDispAdj.
    Context (H : preserves_bincoproduct (pr112 a)).

    Local Definition disp_left_adjoint_univ_cat_with_bincoprod_1cell
      : CC₁ -->[ a ] CC₂.
    Proof.
      refine (_ ,, tt).
      exact (left_adjoint_preserves_bincoproduct
               _
               (left_adjoint_to_is_left_adjoint a)).
    Defined.

    Let F := disp_left_adjoint_univ_cat_with_bincoprod_1cell.

    Local Definition disp_left_adjoint_data_univ_cat_with_bincoprod
      : disp_left_adjoint_data a F.
    Proof.
      refine ((H ,, tt) ,, ((tt ,, tt) ,, (tt ,, tt))).
    Defined.

    Local Definition disp_left_adjoint_axioms_univ_cat_with_bincoprod
      : disp_left_adjoint_axioms a disp_left_adjoint_data_univ_cat_with_bincoprod.
    Proof.
      split ; apply disp_2cells_isaprop_subbicat.
    Qed.

    Local Definition disp_left_adjoint_univ_cat_with_bincoprod
      : disp_left_adjoint a F.
    Proof.
      simple refine (_ ,, _).
      - exact disp_left_adjoint_data_univ_cat_with_bincoprod.
      - exact disp_left_adjoint_axioms_univ_cat_with_bincoprod.
    Defined.

    Definition disp_adjunction_univ_cat_with_bincoprod
      : disp_adjunction a CC₁ CC₂.
    Proof.
      simple refine (_ ,, _).
      - exact F.
      - exact disp_left_adjoint_univ_cat_with_bincoprod.
    Defined.
  End MakeDispAdj.

  Definition disp_adj_weq_preserves_bincoprod
    : disp_adjunction a CC₁ CC₂ ≃ preserves_bincoproduct (pr112 a).
  Proof.
    use weqimplimpl.
    - intro aa.
      apply aa.
    - exact disp_adjunction_univ_cat_with_bincoprod.
    - apply isaprop_disp_adjunction_univ_cat_with_bincoprod.
    - apply isaprop_preserves_bincoproduct.
  Defined.
End DispAdjunctionCoprod.
