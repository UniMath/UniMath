(*******************************************************************************************

 Lifting displayed bicategories

 In this file, we construct the lift of a displayed bicategory. Suppose, that we have a
 bicategory `B` and two displayed bicategories `D₁` and `D₂` over `B`. There are multiple
 ways to form the total bicategory where we combine `D₁` and `D₂`. The first way is by
 taking the product.

 However, in some situations, one would like to take another approach. Instead of viewing
 `D₂` as a displayed bicategory over `D₁`, we view `D₂` as a displayed bicategory over the
 total bicategory `∫ D₁` of `D₁`. We call this construct the lift of `D₂` along `D₁`, and
 in fact, it is the reindexing of `D₂` along the forgetful pseudofunctor `∫ D₁ ⟶ B`.

 One reason why one might to use this construction, can be seen in the study of comprehension
 categories. On top of the bicategory of comprehension categories, one could define numerous
 displayed bicategories, which represent a variety of type formers. However, in some cases,
 one would study full comprehension categories instead. One could define full comprehension
 categories via a displayed bicategory over the bicategory of comprehension categories, and
 the lifting construction defined in this file, allows one to lift the displayed bicategories
 (that represent type formers) to full comprehension categories.

 Contents
 1. The lift of a displayed bicategory
 2. Invertible 2-cells in the lift
 3. Adjoints equivalences in the lift
 4. The univalence of the lift
 5. Properties of the lift

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp.

Section LiftDispBicat.
  Context {B : bicat}
          (D₁ D₂ : disp_bicat B).

  Let E : bicat := total_bicat D₁.

  (** * 1. The lift of a displayed bicategory *)
  Definition lift_disp_cat_ob_mor
    : disp_cat_ob_mor E.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, D₂ (pr1 x)).
    - exact (λ x y xx yy f, xx -->[ pr1 f ] yy).
  Defined.

  Definition lift_disp_cat_id_comp
    : disp_cat_id_comp E lift_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, id_disp _).
    - exact (λ x y z f g xx yy zz ff gg, ff ;; gg).
  Defined.

  Definition lift_disp_cat_data
    : disp_cat_data E.
  Proof.
    simple refine (_ ,, _).
    - exact lift_disp_cat_ob_mor.
    - exact lift_disp_cat_id_comp.
  Defined.

  Definition lift_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells E.
  Proof.
    simple refine (_ ,, _).
    - exact lift_disp_cat_data.
    - exact (λ x y f g τ xx yy ff gg, ff ==>[ pr1 τ ] gg).
  Defined.

  Definition lift_disp_prebicat_ops
    : disp_prebicat_ops lift_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros.
      apply disp_id2.
    - intros.
      apply disp_lunitor.
    - intros.
      apply disp_runitor.
    - intros.
      apply disp_linvunitor.
    - intros.
      apply disp_rinvunitor.
    - intros.
      apply disp_rassociator.
    - intros.
      apply disp_lassociator.
    - intros x y f g h τ θ xx yy zz ff gg ττ θθ.
      exact (ττ •• θθ).
    - intros x y z f g₁ g₂ τ xx yy zz ff gg₁ gg₂ ττ.
      exact (ff ◃◃ ττ).
    - intros x y z f₁ f₂ g τ xx yy zz ff₁ ff₂ gg ττ.
      exact (ττ ▹▹ gg).
  Defined.

  Definition lift_disp_prebicat_data
    : disp_prebicat_data E.
  Proof.
    simple refine (_ ,, _).
    - exact lift_disp_prebicat_1_id_comp_cells.
    - exact lift_disp_prebicat_ops.
  Defined.

  Proposition lift_transportf
              {x y : E}
              {f g : x --> y}
              {τ₁ τ₂ : f ==> g}
              (p : τ₁ = τ₂)
              {xx : lift_disp_prebicat_data x}
              {yy : lift_disp_prebicat_data y}
              {ff : xx -->[ f ] yy}
              {gg : xx -->[ g ] yy}
              (ττ : ff ==>[ τ₁ ] gg)
    : transportf (λ (τ : f ==> g), ff ==>[ τ ] gg) p ττ
      =
      transportf (λ (τ : pr1 f ==> pr1 g), ff ==>[ τ ] gg) (maponpaths pr1 p) ττ.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Proposition lift_transportb
              {x y : E}
              {f g : x --> y}
              {τ₁ τ₂ : f ==> g}
              (p : τ₁ = τ₂)
              {xx : lift_disp_prebicat_data x}
              {yy : lift_disp_prebicat_data y}
              {ff : xx -->[ f ] yy}
              {gg : xx -->[ g ] yy}
              (ττ : ff ==>[ τ₂ ] gg)
    : transportb (λ (τ : f ==> g), ff ==>[ τ ] gg) p ττ
      =
      transportb (λ (τ : pr1 f ==> pr1 g), ff ==>[ τ ] gg) (maponpaths pr1 p) ττ.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Proposition lift_disp_prebicat_laws
    : disp_prebicat_laws lift_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; rewrite lift_transportb.
    - refine (disp_id2_left _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_id2_right _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vassocr _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_id2 _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_id2_rwhisker _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_vcomp _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_vcomp _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_lunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_runitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lwhisker_lwhisker _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_lwhisker _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rwhisker_rwhisker _ _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_vcomp_whisker _ _ _ _ _ _ _ _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lunitor_linvunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_linvunitor_lunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_runitor_rinvunitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rinvunitor_runitor _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lassociator_rassociator _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_rassociator_lassociator _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_runitor_rwhisker _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
    - refine (disp_lassociator_lassociator _ _ _ _ @ _).
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition lift_disp_prebicat
    : disp_prebicat E.
  Proof.
    simple refine (_ ,, _).
    - exact lift_disp_prebicat_data.
    - exact lift_disp_prebicat_laws.
  Defined.

  Definition lift_disp_bicat
    : disp_bicat E.
  Proof.
    refine (lift_disp_prebicat ,, _).
    abstract
      (intros x y f g τ xx yy ff gg ;
       apply disp_cellset_property).
  Defined.

  (** * 2. Invertible 2-cells in the lift *)
  Section DispInvertibleCell.
    Context {x y : E}
            {f g : x --> y}
            (τ : f ==> g)
            (Hτ : is_invertible_2cell τ)
            {xx : lift_disp_bicat x}
            {yy : lift_disp_bicat y}
            {ff : xx -->[ f ] yy}
            {gg : xx -->[ g ] yy}
            (ττ : ff ==>[ τ ] gg).

    Definition to_is_disp_invertible_2cell_lift
               (Hττ : is_disp_invertible_2cell
                        (D := D₂)
                        (pr1_invertible_2cell_total _ Hτ)
                        ττ)
      : is_disp_invertible_2cell Hτ ττ.
    Proof.
      refine (pr1 Hττ ,, _ ,, _).
      - abstract
          (rewrite lift_transportb ;
           exact (pr12 Hττ)).
      - abstract
          (rewrite lift_transportb ;
           exact (pr22 Hττ)).
    Defined.

    Definition from_is_disp_invertible_2cell_lift
               (Hττ : is_disp_invertible_2cell Hτ ττ)
      : is_disp_invertible_2cell
          (D := D₂)
          (pr1_invertible_2cell_total _ Hτ)
          ττ.
    Proof.
      refine (pr1 Hττ ,, _ ,, _).
      - abstract
          (refine (pr12 Hττ @ _) ;
           rewrite lift_transportb ;
           apply idpath).
      - abstract
          (refine (pr22 Hττ @ _) ;
           rewrite lift_transportb ;
           apply idpath).
    Defined.

    Definition is_disp_invertible_2cell_weq_lift
      : is_disp_invertible_2cell
          (D := D₂)
          (pr1_invertible_2cell_total _ Hτ)
          ττ
        ≃
        is_disp_invertible_2cell Hτ ττ.
    Proof.
      use weqimplimpl.
      - apply to_is_disp_invertible_2cell_lift.
      - apply from_is_disp_invertible_2cell_lift.
      - use (isaprop_is_disp_invertible_2cell (x := (_ ,, _))).
      - use (isaprop_is_disp_invertible_2cell (x := (_ ,, _))).
    Defined.
  End DispInvertibleCell.

  Definition disp_invertible_2cell_weq_lift
             {x y : E}
             {f g : x --> y}
             (τ : invertible_2cell f g)
             {xx : lift_disp_bicat x}
             {yy : lift_disp_bicat y}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : disp_invertible_2cell
        (D := D₂)
        (make_invertible_2cell (pr1_invertible_2cell_total _ τ))
        ff gg
      ≃
      disp_invertible_2cell τ ff gg.
  Proof.
    use weqfibtototal.
    intro ττ.
    apply is_disp_invertible_2cell_weq_lift.
  Defined.

  Section DispInvertibleCellOverId.
    Context {x y : E}
            {f : x --> y}
            {xx : lift_disp_bicat x}
            {yy : lift_disp_bicat y}
            {ff gg : xx -->[ f ] yy}
            (ττ : ff ==>[ id2 _ ] gg).

    Definition to_is_disp_invertible_2cell_over_id_lift
               (Hττ : is_disp_invertible_2cell
                        (D := D₂)
                        (id2_invertible_2cell _)
                        ττ)
      : is_disp_invertible_2cell (id2_invertible_2cell _) ττ.
    Proof.
      refine (pr1 Hττ ,, _ ,, _).
      - abstract
          (rewrite lift_transportb ;
           refine (pr12 Hττ @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      - abstract
          (rewrite lift_transportb ;
           refine (pr22 Hττ @ _) ;
           apply maponpaths_2 ;
           apply cellset_property).
    Defined.

    Definition from_is_disp_invertible_2cell_over_id_lift
               (Hττ : is_disp_invertible_2cell (id2_invertible_2cell _) ττ)
      : is_disp_invertible_2cell
          (D := D₂)
          (id2_invertible_2cell _)
          ττ.
    Proof.
      refine (pr1 Hττ ,, _ ,, _).
      - abstract
          (refine (pr12 Hττ @ _) ;
           rewrite lift_transportb ;
           apply maponpaths_2 ;
           apply cellset_property).
      - abstract
          (refine (pr22 Hττ @ _) ;
           rewrite lift_transportb ;
           apply maponpaths_2 ;
           apply cellset_property).
    Defined.

    Definition is_disp_invertible_2cell_over_id_weq_lift
      : is_disp_invertible_2cell
          (D := D₂)
          (id2_invertible_2cell _)
          ττ
        ≃
        is_disp_invertible_2cell (id2_invertible_2cell _) ττ.
    Proof.
      use weqimplimpl.
      - apply to_is_disp_invertible_2cell_over_id_lift.
      - apply from_is_disp_invertible_2cell_over_id_lift.
      - use isaprop_is_disp_invertible_2cell.
      - use isaprop_is_disp_invertible_2cell.
    Defined.
  End DispInvertibleCellOverId.

  Definition disp_invertible_2cell_over_id_weq_lift
             {x y : E}
             {f : x --> y}
             {xx : lift_disp_bicat x}
             {yy : lift_disp_bicat y}
             (ff gg : xx -->[ f ] yy)
    : disp_invertible_2cell
        (D := D₂)
        (id2_invertible_2cell _)
        ff gg
      ≃
      disp_invertible_2cell (id2_invertible_2cell f) ff gg.
  Proof.
    use weqfibtototal.
    intro ττ.
    apply is_disp_invertible_2cell_over_id_weq_lift.
  Defined.

  (** * 3. Adjoints equivalences in the lift *)
  Section DispAdjEquivOverId.
    Context {x : E}
            {xx yy : lift_disp_bicat x}
            (ff : xx -->[ identity _ ] yy).

    Section ToLift.
      Context (Hff : disp_left_adjoint_equivalence
                       (internal_adjoint_equivalence_identity (pr1 x))
                       ff).

      Definition to_disp_left_adjoint_equivalence_over_id_lift_data
        : disp_left_adjoint_data (internal_adjoint_equivalence_identity x) ff
        := pr11 Hff ,, (pr121 Hff ,, pr221 Hff).

      Proposition to_disp_left_adjoint_equivalence_over_id_lift_axioms
        : disp_left_adjoint_axioms
            (internal_adjoint_equivalence_identity x)
            to_disp_left_adjoint_equivalence_over_id_lift_data.
      Proof.
        split.
        - refine (pr112 Hff @ _).
          rewrite lift_transportb.
          apply maponpaths_2.
          apply cellset_property.
        - refine (pr212 Hff @ _).
          rewrite lift_transportb.
          apply maponpaths_2.
          apply cellset_property.
      Qed.

      Proposition to_disp_left_adjoint_equivalence_over_id_lift_inv
        : disp_left_equivalence_axioms
            (internal_adjoint_equivalence_identity x)
            to_disp_left_adjoint_equivalence_over_id_lift_data.
      Proof.
        split.
        - pose (H := pr122 Hff).
          simple refine (_ ,, _ ,, _).
          + exact (pr1 H).
          + refine (pr12 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
          + refine (pr22 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
        - pose (H := pr222 Hff).
          simple refine (_ ,, _ ,, _).
          + exact (pr1 H).
          + refine (pr12 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
          + refine (pr22 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
      Qed.

      Definition to_disp_left_adjoint_equivalence_over_id_lift
        : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity x) ff.
      Proof.
        refine (to_disp_left_adjoint_equivalence_over_id_lift_data ,, _).
        split.
        - exact to_disp_left_adjoint_equivalence_over_id_lift_axioms.
        - exact to_disp_left_adjoint_equivalence_over_id_lift_inv.
      Defined.
    End ToLift.

    Section FromLift.
      Context (Hff : disp_left_adjoint_equivalence
                       (internal_adjoint_equivalence_identity x)
                       ff).

      Definition from_disp_left_adjoint_equivalence_over_id_lift_data
        : disp_left_adjoint_data (internal_adjoint_equivalence_identity (pr1 x)) ff
        := pr11 Hff ,, (pr121 Hff ,, pr221 Hff).

      Proposition from_disp_left_adjoint_equivalence_over_id_lift_axioms
        : disp_left_adjoint_axioms
            (internal_adjoint_equivalence_identity (pr1 x))
            from_disp_left_adjoint_equivalence_over_id_lift_data.
      Proof.
        split.
        - refine (pr112 Hff @ _).
          rewrite lift_transportb.
          apply maponpaths_2.
          apply cellset_property.
        - refine (pr212 Hff @ _).
          rewrite lift_transportb.
          apply maponpaths_2.
          apply cellset_property.
      Qed.

      Proposition from_disp_left_adjoint_equivalence_over_id_lift_inv
        : disp_left_equivalence_axioms
            (internal_adjoint_equivalence_identity (pr1 x))
            from_disp_left_adjoint_equivalence_over_id_lift_data.
      Proof.
        split.
        - pose (H := pr122 Hff).
          simple refine (_ ,, _ ,, _).
          + exact (pr1 H).
          + refine (pr12 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
          + refine (pr22 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
        - pose (H := pr222 Hff).
          simple refine (_ ,, _ ,, _).
          + exact (pr1 H).
          + refine (pr12 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
          + refine (pr22 H @ _).
            rewrite lift_transportb.
            apply maponpaths_2.
            apply cellset_property.
      Qed.

      Definition from_disp_left_adjoint_equivalence_over_id_lift
        : disp_left_adjoint_equivalence
            (internal_adjoint_equivalence_identity (pr1 x))
            ff.
      Proof.
        refine (from_disp_left_adjoint_equivalence_over_id_lift_data ,, _).
        split.
        - exact from_disp_left_adjoint_equivalence_over_id_lift_axioms.
        - exact from_disp_left_adjoint_equivalence_over_id_lift_inv.
      Defined.
    End FromLift.

    Proposition disp_left_adjoint_equivalence_over_id_weq_lift_left
                (Hff : disp_left_adjoint_equivalence
                         (internal_adjoint_equivalence_identity (pr1 x))
                         ff)
      : from_disp_left_adjoint_equivalence_over_id_lift
          (to_disp_left_adjoint_equivalence_over_id_lift Hff)
        =
        Hff.
    Proof.
      use subtypePath.
      {
        intro.
        use isapropdirprod.
        - use isapropdirprod ; apply disp_cellset_property.
        - use isapropdirprod ; use isaprop_is_disp_invertible_2cell.
      }
      apply idpath.
    Qed.

    Proposition disp_left_adjoint_equivalence_over_id_weq_lift_right
                (Hff : disp_left_adjoint_equivalence
                         (internal_adjoint_equivalence_identity x)
                         ff)
      : to_disp_left_adjoint_equivalence_over_id_lift
          (from_disp_left_adjoint_equivalence_over_id_lift Hff)
        =
        Hff.
    Proof.
      use subtypePath.
      {
        intro.
        use isapropdirprod.
        - use isapropdirprod ; apply disp_cellset_property.
        - use isapropdirprod ; use isaprop_is_disp_invertible_2cell.
      }
      apply idpath.
    Qed.

    Definition disp_left_adjoint_equivalence_over_id_weq_lift
      : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity (pr1 x)) ff
        ≃
        disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity x) ff.
    Proof.
      use weq_iso.
      - exact to_disp_left_adjoint_equivalence_over_id_lift.
      - exact from_disp_left_adjoint_equivalence_over_id_lift.
      - exact disp_left_adjoint_equivalence_over_id_weq_lift_left.
      - exact disp_left_adjoint_equivalence_over_id_weq_lift_right.
    Defined.
  End DispAdjEquivOverId.

  Definition disp_adjequiv_over_id_weq_lift
             {x : E}
             (xx yy : lift_disp_bicat x)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity (pr1 x)) xx yy
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
  Proof.
    use weqfibtototal.
    intro ff.
    exact (disp_left_adjoint_equivalence_over_id_weq_lift ff).
  Defined.

  (** * 4. The univalence of the lift *)
  Proposition disp_univalent_2_1_lift_disp_bicat
              (HD : disp_univalent_2_1 D₂)
    : disp_univalent_2_1 lift_disp_bicat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros x y f xx yy ff gg.
    use weqhomot.
    - exact (disp_invertible_2cell_over_id_weq_lift ff gg
             ∘ make_weq _ (HD _ _ _ _ (idpath _) _ _ ff gg))%weq.
    - intro p ; cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use isaprop_is_disp_invertible_2cell.
      }
      cbn.
      apply idpath.
  Qed.

  Proposition disp_univalent_2_0_lift_disp_bicat
              (HD₁ : disp_univalent_2_0 D₂)
              (HD₂ : disp_univalent_2_1 D₂)
              (HB : is_univalent_2_1 B)
              (HD' : disp_univalent_2_1 D₁)
    : disp_univalent_2_0 lift_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x xx yy.
    use weqhomot.
    - exact (disp_adjequiv_over_id_weq_lift xx yy
             ∘ make_weq _ (HD₁ _ _ (idpath _) xx yy))%weq.
    - intro p ; cbn in p.
      induction p.
      use subtypePath.
      {
        intro.
        use (isaprop_disp_left_adjoint_equivalence).
        - exact (total_is_univalent_2_1 _ HB HD').
        - use disp_univalent_2_1_lift_disp_bicat.
          exact HD₂.
      }
      cbn.
      apply idpath.
  Qed.

  (** * 5. Properties of the lift *)
  Definition disp_2cells_isaprop_lift_disp_bicat
             (HD : disp_2cells_isaprop D₂)
    : disp_2cells_isaprop lift_disp_bicat.
  Proof.
    intros x y f g τ xx yy ff gg.
    apply HD.
  Qed.

  Definition disp_locally_groupoid_lift_disp_bicat
             (HD : disp_locally_groupoid D₂)
    : disp_locally_groupoid lift_disp_bicat.
  Proof.
    intros x y f g τ xx yy ff gg ττ.
    use to_is_disp_invertible_2cell_lift.
    use (HD _ _ _ _ (_ ,, _)).
  Defined.

  Definition disp_2cells_iscontr_lift_disp_bicat
             (HD : disp_2cells_iscontr D₂)
    : disp_2cells_iscontr lift_disp_bicat.
  Proof.
    intros x y f g τ xx yy ff gg.
    apply HD.
  Qed.
End LiftDispBicat.
