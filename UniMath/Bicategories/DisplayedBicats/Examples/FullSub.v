(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Full subbicategory of a bicategory and proof that it's univalent.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* ----------------------------------------------------------------------------------- *)
(** Full sub-bicategory associated to a bicategory and a predicate on objects          *)
(* ----------------------------------------------------------------------------------- *)
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

  Definition fullsub : UU := fullsubbicat.

  Definition morfullsub
             (X Y : fullsub)
    : UU
    := fullsubbicat⟦X,Y⟧.

  Definition cellfullsub
             {X Y : fullsub}
             (f g : morfullsub X Y)
    : UU
    := f ==> g.

  Coercion ob_of_fullsub
           (X : fullsub)
    : ob C
    := pr1 X.

  Coercion fullsub_to_mor
           {X Y : fullsub}
           (f : morfullsub X Y)
    : C⟦pr1 X,pr1 Y⟧
    := pr1 f.

  Coercion fullsub_to_cell
           {X Y : fullsub}
           {f g : morfullsub X Y}
           (α : cellfullsub f g)
    : prebicat_cells C f g
    := pr1 α.

  Definition mor_of_fullsub
             {X Y : fullsub}
             (f : @precategory_morphisms C X Y)
    : morfullsub X Y
    := (f ,, tt).

  Definition cell_of_fullsub
             {X Y : fullsubbicat}
             {f g : X --> Y}
             (α : pr1 f ==> pr1 g)
    : f ==> g
    := (α ,, tt).

  Definition fullsub_is_invertible_2cell_to_bicat_is_invertible_2cell
             {X Y : fullsubbicat}
             {f g : X --> Y}
             (α : f ==> g)
    : is_invertible_2cell α → @is_invertible_2cell C (pr1 X) (pr1 Y) (pr1 f) (pr1 g) (pr1 α).
  Proof.
    intros Hα.
    use tpair.
    - apply Hα.
    - split ; cbn.
      + exact (base_paths _ _ (vcomp_rinv Hα)).
      + exact (base_paths _ _ (vcomp_lid Hα)).
  Defined.

  Definition bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell
             {X Y : fullsubbicat}
             {f g : X --> Y}
             (α : f ==> g)
    : @is_invertible_2cell C (pr1 X) (pr1 Y) (pr1 f) (pr1 g) (pr1 α) → is_invertible_2cell α.
  Proof.
    intros Hα.
    use tpair.
    - refine (_ ,, tt).
      apply Hα.
    - split ; use subtypePath.
      + intro ; apply isapropunit.
      + apply Hα.
      + intro ; apply isapropunit.
      + apply Hα.
  Defined.

  Definition bicat_is_invertible_2cell_is_fullsub_is_invertible_2cell
             {X Y : fullsubbicat}
             {f g : X --> Y}
             (α : f ==> g)
    : @is_invertible_2cell C (pr1 X) (pr1 Y) (pr1 f) (pr1 g) (pr1 α) ≃ is_invertible_2cell α.
  Proof.
    use weqimplimpl.
    - exact (bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell α).
    - exact (fullsub_is_invertible_2cell_to_bicat_is_invertible_2cell α).
    - apply isaprop_is_invertible_2cell.
    - apply isaprop_is_invertible_2cell.
  Defined.

  Definition disp_fullsubbicat_univalent_2_1
    : disp_univalent_2_1 disp_fullsubbicat.
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros x y f xx yy ff gg.
    use isweqimplimpl.
    - intros.
      apply isapropunit.
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
    apply total_is_univalent_2_1.
    - exact HC.
    - exact disp_fullsubbicat_univalent_2_1.
  Defined.

  Definition fullsub_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence
             {X Y : fullsubbicat}
             (f : X --> Y)
    : left_adjoint_equivalence f → @left_adjoint_equivalence C (pr1 X) (pr1 Y) (pr1 f).
  Proof.
    intros Hf.
    use tpair.
    - use tpair.
      + exact (pr1 (left_adjoint_right_adjoint Hf)).
      + split.
        * exact (pr1 (left_adjoint_unit Hf)).
        * exact (pr1 (left_adjoint_counit Hf)).
    - split ; split.
      + exact (base_paths _ _ (internal_triangle1 Hf)).
      + exact (base_paths _ _ (internal_triangle2 Hf)).
      + cbn.
        apply (fullsub_is_invertible_2cell_to_bicat_is_invertible_2cell
                 (left_adjoint_unit (pr1 Hf))).
        apply Hf.
      + cbn.
        apply (fullsub_is_invertible_2cell_to_bicat_is_invertible_2cell
                 (left_adjoint_counit (pr1 Hf))).
        apply Hf.
  Defined.

  Definition bicat_left_adjoint_equivalence_to_fullsub_left_adjoint_equivalence
             {X Y : fullsubbicat}
             (f : X --> Y)
    : @left_adjoint_equivalence C (pr1 X) (pr1 Y) (pr1 f) → left_adjoint_equivalence f.
  Proof.
    intros Hf.
    use tpair.
    - use tpair.
      + exact (left_adjoint_right_adjoint Hf ,, tt).
      + split.
        * exact (left_adjoint_unit Hf ,, tt).
        * exact (left_adjoint_counit Hf ,, tt).
    - split ; split.
      + use subtypePath.
        * intro ; apply isapropunit.
        * exact (internal_triangle1 Hf).
      + use subtypePath.
        * intro ; apply isapropunit.
        * exact (internal_triangle2 Hf).
      + apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
        apply Hf.
      + apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
        apply Hf.
  Defined.

  Definition fullsub_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence
             {X Y : fullsubbicat}
             (f : X --> Y)
    : left_adjoint_equivalence f ≃ @left_adjoint_equivalence C (pr1 X) (pr1 Y) (pr1 f).
  Proof.
    use make_weq.
    - exact (fullsub_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence f).
    - use isweq_iso.
      + exact (bicat_left_adjoint_equivalence_to_fullsub_left_adjoint_equivalence f).
      + intros x.
        use subtypePath.
        * intro.
          do 2 apply isapropdirprod.
          ** apply fullsubbicat.
          ** apply fullsubbicat.
          ** apply isaprop_is_invertible_2cell.
          ** apply isaprop_is_invertible_2cell.
        * induction x as [a hx].
          induction a as [r uc].
          induction uc as [η ε].
          induction r as [r x].
          induction x.
          induction η as [η x].
          induction x.
          induction ε as [ε x].
          induction x.
          cbn in *.
          reflexivity.
      + intros x.
        use subtypePath.
        * intro.
          do 2 apply isapropdirprod ; try (apply C) ; apply isaprop_is_invertible_2cell.
        * reflexivity.
  Defined.

  Definition bicat_adjoint_equivalence_is_fullsub_adjoint_equivalence
             (X Y : fullsubbicat)
    : @adjoint_equivalence C (pr1 X) (pr1 Y) ≃ adjoint_equivalence X Y.
  Proof.
    apply invweq.
    use weqtotal2.
    - apply invweq.
      apply weqtodirprodwithunit.
    - intro ; cbn.
      apply fullsub_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence.
  Defined.

  Definition disp_univalent_2_0_fullsubbicat
             (HC : is_univalent_2 C)
             (HP : ∏ (x : C), isaprop (P x))
    : disp_univalent_2_0 disp_fullsubbicat.
  Proof.
    intros x y p xx yy.
    induction p.
    use isweqimplimpl.
    - intros ; cbn in *.
      apply HP.
    - apply isasetaprop.
      apply HP.
    - simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
      + exact isapropunit.
      + apply isaprop_disp_left_adjoint_equivalence.
        * apply (pr2 HC).
        * exact disp_fullsubbicat_univalent_2_1.
  Defined.

  Definition is_univalent_2_0_fullsubbicat
             (HC : is_univalent_2 C)
             (HP : ∏ (x : C), isaprop (P x))
    : is_univalent_2_0 fullsubbicat.
  Proof.
    apply total_is_univalent_2_0.
    - exact (pr1 HC).
    - exact (disp_univalent_2_0_fullsubbicat HC HP).
  Defined.

  Definition is_univalent_2_fullsubbicat
             (HC : is_univalent_2 C)
             (HP : ∏ (x : C), isaprop (P x))
    : is_univalent_2 fullsubbicat.
  Proof.
    split.
    - apply is_univalent_2_0_fullsubbicat; assumption.
    - apply is_univalent_2_1_fullsubbicat.
      exact (pr2 HC).
  Defined.

  Definition disp_2cells_isaprop_fullsubbicat
    : disp_2cells_isaprop disp_fullsubbicat.
  Proof.
    intro; intros; exact isapropunit.
  Qed.

  Definition disp_locally_groupoid_fullsubbicat
    : disp_locally_groupoid disp_fullsubbicat.
  Proof.
    use make_disp_locally_groupoid.
    - intro; intros. exact tt.
    - exact disp_2cells_isaprop_fullsubbicat.
  Qed.

End FullSubBicat.
