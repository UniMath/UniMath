(***************************************************************************
 Properties of the bicat of pseudofunctors

 In this file, we study some properties of the bicategory of pseudofunctors.
 We look at the following properties:
 1. Being locally groupoidal
 2. Terminal objects
 3. Initial objects
 ***************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Colimits.Final.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.

Local Open Scope cat.

(** 1. Locally groupoidal *)
Section FixALocallyGrpd.
  Context (B₁ : bicat)
          {B₂ : bicat}
          (HB₂ : locally_groupoid B₂).

  Definition locally_groupoid_psfunctor_bicat
    : locally_groupoid (psfunctor_bicat B₁ B₂).
  Proof.
    intros F G α β m.
    use make_is_invertible_modification.
    intro x.
    apply HB₂.
  Defined.
End FixALocallyGrpd.

(** 2. Final objects *)
Section FixAFinal.
  Context (B₁ : bicat)
          {B₂ : bicat}
          {HB₂_2_1 : is_univalent_2_1 B₂}
          (f : BiFinal HB₂_2_1).

  Definition final_psfunctor
    : psfunctor_bicat B₁ B₂
    := constant _ (pr1 f).

  Definition final_psfunctor_1cell_data
             (F : psfunctor B₁ B₂)
    : pstrans_data F final_psfunctor.
  Proof.
    use make_pstrans_data.
    - exact (λ x, bifinal_1cell _ (pr2 f) (F x)).
    - intros x y g.
      apply (bifinal_2cell _ (pr2 f)).
  Defined.

  Definition final_psfunctor_1cell_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (final_psfunctor_1cell_data F).
  Proof.
    repeat split ; intros ; apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition final_psfunctor_1cell
             (F : psfunctor B₁ B₂)
    : pstrans F final_psfunctor.
  Proof.
    use make_pstrans.
    - exact (final_psfunctor_1cell_data F).
    - exact (final_psfunctor_1cell_is_pstrans F).
  Defined.

  Definition final_psfunctor_2cell_data
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : invertible_modification_data α β
    := λ x, bifinal_2cell _ (pr2 f) (α x) (β x).

  Definition final_psfunctor_2cell_is_modification
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : is_modification (final_psfunctor_2cell_data α β).
  Proof.
    intros x y g.
    apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition final_psfunctor_2cell
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : invertible_modification α β.
  Proof.
    use make_invertible_modification.
    - exact (final_psfunctor_2cell_data α β).
    - exact (final_psfunctor_2cell_is_modification α β).
  Defined.

  Definition final_psfunctor_eq
             {F : psfunctor B₁ B₂}
             {α β : pstrans F final_psfunctor}
             (m₁ m₂ : modification α β)
    : m₁ = m₂.
  Proof.
    use modification_eq.
    intro.
    apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition psfunctor_bifinal
    : BiFinal (psfunctor_bicat_is_univalent_2_1 B₁ B₂ HB₂_2_1).
  Proof.
    simple refine (_ ,, _).
    - exact final_psfunctor.
    - use is_bifinal'_to_is_bifinal.
      use make_is_bifinal'.
      + exact final_psfunctor_1cell.
      + exact @final_psfunctor_2cell.
      + exact @final_psfunctor_eq.
  Defined.
End FixAFinal.

(** 3. Initial objects *)
Section FixAnInitial.
  Context (B₁ : bicat)
          {B₂ : bicat}
          {HB₂_2_1 : is_univalent_2_1 B₂}
          (i : BiInitial HB₂_2_1).

  Definition initial_psfunctor
    : psfunctor_bicat B₁ B₂
    := constant _ (pr1 i).

  Definition initial_psfunctor_1cell_data
             (F : psfunctor B₁ B₂)
    : pstrans_data initial_psfunctor F.
  Proof.
    use make_pstrans_data.
    - exact (λ x, biinitial_1cell _ (pr2 i) (F x)).
    - intros x y g.
      apply (biinitial_2cell _ (pr2 i)).
  Defined.

  Definition initial_psfunctor_1cell_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (initial_psfunctor_1cell_data F).
  Proof.
    repeat split ; intros ; apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition initial_psfunctor_1cell
             (F : psfunctor B₁ B₂)
    : pstrans initial_psfunctor F.
  Proof.
    use make_pstrans.
    - exact (initial_psfunctor_1cell_data F).
    - exact (initial_psfunctor_1cell_is_pstrans F).
  Defined.

  Definition initial_psfunctor_2cell_data
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : invertible_modification_data α β
    := λ x, biinitial_2cell _ (pr2 i) (α x) (β x).

  Definition initial_psfunctor_2cell_is_modification
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : is_modification (initial_psfunctor_2cell_data α β).
  Proof.
    intros x y g.
    apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition initial_psfunctor_2cell
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : invertible_modification α β.
  Proof.
    use make_invertible_modification.
    - exact (initial_psfunctor_2cell_data α β).
    - exact (initial_psfunctor_2cell_is_modification α β).
  Defined.

  Definition initial_psfunctor_eq
             {F : psfunctor B₁ B₂}
             {α β : pstrans initial_psfunctor F}
             (m₁ m₂ : modification α β)
    : m₁ = m₂.
  Proof.
    use modification_eq.
    intro.
    apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition psfunctor_biinitial
    : BiInitial (psfunctor_bicat_is_univalent_2_1 B₁ B₂ HB₂_2_1).
  Proof.
    simple refine (_ ,, _).
    - exact initial_psfunctor.
    - use is_biinitial'_to_is_biinitial.
      use make_is_biinitial'.
      + exact initial_psfunctor_1cell.
      + exact @initial_psfunctor_2cell.
      + exact @initial_psfunctor_eq.
  Defined.
End FixAnInitial.

(*
This is WIP. It is commented out, because it needs refactoring

Section FixProducts.
  Context (B₁ : bicat)
          (B₂ : bicat_with_binprod).

  Section BinprodPSFunctor.
    Context (F G : psfunctor B₁ B₂).

    Definition binprod_psfunctor_data
      : psfunctor_data B₁ B₂.
    Proof.
      use make_psfunctor_data.
      - exact (λ z, F z ⊗ G z).
      - exact (λ x y f, #F f ⊗₁ #G f).
      - exact (λ x y f g α, ##F α ⊗₂ ##G α).
      - exact (λ b,
               (pair_1cell_id_id_invertible B₂ (F b) (G b))^-1
               • psfunctor_id F b ⊗₂ psfunctor_id G b).
      - exact (λ b₁ b₂ b₃ f g,
               pair_1cell_comp _ (#F f) (#F g) (#G f) (#G g)
               • psfunctor_comp F f g ⊗₂ psfunctor_comp G f g).
    Defined.

    Definition binprod_psfunctor_laws
      : psfunctor_laws binprod_psfunctor_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f ; cbn.
        rewrite !psfunctor_id2.
        rewrite pair_2cell_id_id.
        apply idpath.
      - intros b₁ b₂ f g h α β ; cbn.
        rewrite !psfunctor_vcomp.
        rewrite !pair_2cell_comp.
        apply idpath.
      - intros b₁ b₂ f ; cbn.
        use binprod_ump_2cell_unique_alt.
        + apply (pr2 B₂).
        + pose (psfunctor_lunitor F f) as Fid.
          pose (psfunctor_lunitor G f) as Gid.
          apply TODO.
        + apply TODO.
      - intros b₁ b₂ f ; cbn.
        use binprod_ump_2cell_unique_alt.
        + apply (pr2 B₂).
        + rewrite <- !lwhisker_vcomp.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                apply binprod_ump_2cell_pr1.
              }
              etrans.
              {
                apply maponpaths_2.
                apply binprod_ump_2cell_pr1.
              }
              rewrite !vassocl.
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                rewrite !vassocr.
                rewrite vcomp_linv.
                rewrite id2_left.
                apply idpath.
              }
              rewrite !vassocr.
              rewrite lwhisker_vcomp.
              apply idpath.
            }
            etrans.
            {
              apply maponpaths_2.
              apply binprod_ump_2cell_pr1.
            }
            rewrite !vassocl.
            etrans.
            {
              do 5 apply maponpaths.
              rewrite !vassocr.
              rewrite vcomp_linv.
              rewrite id2_left.
              apply idpath.
            }
            apply idpath.
          }
          etrans.
          {
            rewrite !vassocr.
            do 6 apply maponpaths_2.
            rewrite !vassocl.
            rewrite <- rwhisker_lwhisker_rassociator.
            rewrite !vassocr.
            rewrite <- rwhisker_lwhisker_rassociator.
            rewrite !vassocl.
            apply maponpaths.
            etrans.
            {
              do 2 apply maponpaths.
              apply binprod_ump_2cell_pr1.
            }
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              apply binprod_ump_2cell_pr1.
            }
            rewrite lwhisker_vcomp.
            apply maponpaths.
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite vcomp_linv.
            rewrite id2_left.
            apply idpath.
          }
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_vcomp.
            rewrite !vassocl.
            rewrite vcomp_linv.
            rewrite id2_right.
            etrans.
            {
              apply maponpaths_2.
              rewrite <- !lwhisker_vcomp.
              apply idpath.
            }
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_lwhisker.
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              rewrite !vassocr.
              rewrite <- vcomp_whisker.
              rewrite !vassocl.
              apply maponpaths.
              rewrite !vassocr.
              rewrite <- lwhisker_lwhisker_rassociator.
              rewrite !vassocl.
              apply maponpaths.
              rewrite !vassocr.
              rewrite lwhisker_vcomp.
              apply maponpaths_2.
              apply maponpaths.
              rewrite !vassocr.
              exact (!(psfunctor_runitor F f)).
            }
            etrans.
            {
              do 2 apply maponpaths.
              rewrite !vassocr.
              rewrite runitor_triangle.
              apply idpath.
            }
            etrans.
            {
              apply maponpaths.
              rewrite !vassocr.
              rewrite vcomp_runitor.
              apply idpath.
            }
            rewrite !vassocr.
            rewrite <- runitor_triangle.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            rewrite id2_left.
            rewrite !vassocl.
            rewrite vcomp_rinv.
            apply id2_right.
          }
          rewrite !lwhisker_vcomp.
          rewrite rinvunitor_runitor.
          rewrite id2_right.
          apply lunitor_lwhisker.
        + rewrite <- !lwhisker_vcomp.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                apply binprod_ump_2cell_pr2.
              }
              etrans.
              {
                apply maponpaths_2.
                apply binprod_ump_2cell_pr2.
              }
              rewrite !vassocl.
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                rewrite !vassocr.
                rewrite vcomp_linv.
                rewrite id2_left.
                apply idpath.
              }
              rewrite !vassocr.
              rewrite lwhisker_vcomp.
              apply idpath.
            }
            etrans.
            {
              apply maponpaths_2.
              apply binprod_ump_2cell_pr2.
            }
            rewrite !vassocl.
            etrans.
            {
              do 5 apply maponpaths.
              rewrite !vassocr.
              rewrite vcomp_linv.
              rewrite id2_left.
              apply idpath.
            }
            apply idpath.
          }
          etrans.
          {
            rewrite !vassocr.
            do 6 apply maponpaths_2.
            rewrite !vassocl.
            rewrite <- rwhisker_lwhisker_rassociator.
            rewrite !vassocr.
            rewrite <- rwhisker_lwhisker_rassociator.
            rewrite !vassocl.
            apply maponpaths.
            etrans.
            {
              do 2 apply maponpaths.
              apply binprod_ump_2cell_pr2.
            }
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              apply binprod_ump_2cell_pr2.
            }
            rewrite lwhisker_vcomp.
            apply maponpaths.
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite vcomp_linv.
            rewrite id2_left.
            apply idpath.
          }
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_vcomp.
            rewrite !vassocl.
            rewrite vcomp_linv.
            rewrite id2_right.
            etrans.
            {
              apply maponpaths_2.
              rewrite <- !lwhisker_vcomp.
              apply idpath.
            }
            rewrite !vassocl.
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_lwhisker.
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths.
              rewrite !vassocr.
              rewrite <- vcomp_whisker.
              rewrite !vassocl.
              apply maponpaths.
              rewrite !vassocr.
              rewrite <- lwhisker_lwhisker_rassociator.
              rewrite !vassocl.
              apply maponpaths.
              rewrite !vassocr.
              rewrite lwhisker_vcomp.
              apply maponpaths_2.
              apply maponpaths.
              rewrite !vassocr.
              exact (!(psfunctor_runitor G f)).
            }
            etrans.
            {
              do 2 apply maponpaths.
              rewrite !vassocr.
              rewrite runitor_triangle.
              apply idpath.
            }
            etrans.
            {
              apply maponpaths.
              rewrite !vassocr.
              rewrite vcomp_runitor.
              apply idpath.
            }
            rewrite !vassocr.
            rewrite <- runitor_triangle.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            rewrite id2_left.
            rewrite !vassocl.
            rewrite vcomp_rinv.
            apply id2_right.
          }
          rewrite !lwhisker_vcomp.
          rewrite rinvunitor_runitor.
          rewrite id2_right.
          apply lunitor_lwhisker.
      - intros b₁ b₂ b₃ b₄ f g h ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g₁ g₂ α ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g₁ g₂ α ; cbn.
        apply TODO.
    Qed.

    Definition binprod_psfunctor_invertible_2cells
      : invertible_cells binprod_psfunctor_data.
    Proof.
      split ; cbn.
      - intros b.
        is_iso.
        + use binprod_ump_2cell_invertible.
          * is_iso.
          * is_iso.
        + use binprod_ump_2cell_invertible.
          * is_iso.
            ** apply property_from_invertible_2cell.
            ** apply psfunctor_id.
          * is_iso.
            ** apply property_from_invertible_2cell.
            ** apply psfunctor_id.
      - intros b₁ b₂ b₃ f g.
        is_iso.
        + apply pair_1cell_comp_invertible.
        + use binprod_ump_2cell_invertible.
          * is_iso.
            ** apply property_from_invertible_2cell.
            ** apply psfunctor_comp.
          * is_iso.
            ** apply property_from_invertible_2cell.
            ** apply psfunctor_comp.
    Defined.

    Definition binprod_psfunctor
      : psfunctor B₁ B₂.
    Proof.
      use make_psfunctor.
      - exact binprod_psfunctor_data.
      - exact binprod_psfunctor_laws.
      - exact binprod_psfunctor_invertible_2cells.
    Defined.

    Definition binprod_psfunctor_pr1_data
      : pstrans_data binprod_psfunctor F.
    Proof.
      use make_pstrans_data.
      - exact (λ x, π₁).
      - cbn.
        simple refine (λ x y f, _).
        use inv_of_invertible_2cell.
        apply pair_1cell_pr1.
    Defined.

    Definition binprod_psfunctor_pr1_is_pstrans
      : is_pstrans binprod_psfunctor_pr1_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f g α ; cbn.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      - intros b ; cbn.
        rewrite <- rwhisker_vcomp.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocr.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite !vassocl.
            rewrite linvunitor_lunitor.
            apply id2_right.
          }
          apply runitor_rinvunitor.
        }
        rewrite id2_left.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr1.
        rewrite !vassocl.
        apply maponpaths.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      - intros b₁ b₂ b₃ f g ; cbn.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 6 apply maponpaths.
          apply pair_2cell_pr1.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        do 4 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator, id2_left.
        rewrite !vassocl.
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
    Qed.

    Definition binprod_psfunctor_pr1
      : pstrans binprod_psfunctor F.
    Proof.
      use make_pstrans.
      - exact binprod_psfunctor_pr1_data.
      - exact binprod_psfunctor_pr1_is_pstrans.
    Defined.

    Definition binprod_psfunctor_pr2_data
      : pstrans_data binprod_psfunctor G.
    Proof.
      use make_pstrans_data.
      - exact (λ x, π₂).
      - cbn.
        simple refine (λ x y f, _).
        use inv_of_invertible_2cell.
        apply pair_1cell_pr2.
    Defined.

    Definition binprod_psfunctor_pr2_is_pstrans
      : is_pstrans binprod_psfunctor_pr2_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f g α ; cbn.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr2.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      - intros b ; cbn.
        rewrite <- rwhisker_vcomp.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocr.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite !vassocl.
            rewrite linvunitor_lunitor.
            apply id2_right.
          }
          apply runitor_rinvunitor.
        }
        rewrite id2_left.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr2.
        rewrite !vassocl.
        apply maponpaths.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      - intros b₁ b₂ b₃ f g ; cbn.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 6 apply maponpaths.
          apply pair_2cell_pr2.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        do 4 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr2.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator, id2_left.
        rewrite !vassocl.
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
    Qed.

    Definition binprod_psfunctor_pr2
      : pstrans binprod_psfunctor G.
    Proof.
      use make_pstrans.
      - exact binprod_psfunctor_pr2_data.
      - exact binprod_psfunctor_pr2_is_pstrans.
    Defined.

    Definition psfunctor_binprod_cone
      : binprod_cone F G.
    Proof.
      use make_binprod_cone.
      - exact binprod_psfunctor.
      - exact binprod_psfunctor_pr1.
      - exact binprod_psfunctor_pr2.
    Defined.

    Definition pstrans_pair_data
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : pstrans_data H binprod_psfunctor.
    Proof.
      use make_pstrans_data.
      - exact (λ x, ⟨ α x , β x ⟩).
      - intros x y f ; simpl.
        use make_invertible_2cell.
        + exact (precomp_prod_1cell _ _ _ _
                 • ⟪ lassociator _ _ _
                     • (prod_1cell_pr1 _ _ _ ▹ _)
                     • psnaturality_of α f
                   ,
                     lassociator _ _ _
                     • (prod_1cell_pr2 _ _ _ ▹ _)
                     • psnaturality_of β f
                   ⟫
                 • (precomp_prod_1cell_invertible _ _ _ _)^-1).
        + is_iso.
          * apply precomp_prod_1cell_invertible.
          * use binprod_ump_2cell_invertible.
            ** is_iso ; apply property_from_invertible_2cell.
            ** is_iso ; apply property_from_invertible_2cell.
    Defined.

    Definition pstrans_pair_is_pstrans
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : is_pstrans (pstrans_pair_data α β).
    Proof.
      repeat split.
      - intros b₁ b₂ f g τ ; cbn.
        use binprod_ump_2cell_unique_alt.
        + apply (pr2 B₂).
        + apply TODO.
        + apply TODO.
      - intros b ; cbn.
        use binprod_ump_2cell_unique_alt.
        + apply (pr2 B₂).
        + rewrite <- !lwhisker_vcomp.
          rewrite <- !rwhisker_vcomp.
          use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite runitor_rwhisker.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply binprod_ump_2cell_pr1.
          }
          rewrite <- !lwhisker_vcomp.
          rewrite !vassocl.
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite <- rwhisker_lwhisker.
            rewrite !vassocl.
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              apply binprod_ump_2cell_pr1.
            }
            rewrite !vassocl.
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_2.
              apply binprod_ump_2cell_pr1.
            }
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            rewrite id2_left.
            rewrite !vassocl.
            rewrite binprod_ump_2cell_pr1.
            etrans.
            {
              do 2 apply maponpaths.
              apply maponpaths_2.
              apply binprod_ump_2cell_pr1.
            }
            rewrite !vassocl.
            apply maponpaths.
            rewrite !vassocr.
            rewrite vcomp_linv.
            rewrite id2_left.
            rewrite !vassocl.
            etrans.
            {
              do 3 apply maponpaths.
              rewrite !vassocr.
              rewrite vcomp_linv.
              rewrite id2_left.
              apply idpath.
            }
            rewrite pstrans_id_alt.
            rewrite !vassocl.
            apply idpath.
          }
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite lwhisker_vcomp.
            rewrite !vassocl.
            rewrite vcomp_linv.
            rewrite id2_right.
            rewrite <- lwhisker_vcomp.
            etrans.
            {
              refine (vassocr _ _ _ @ _).
              apply maponpaths_2.
              rewrite !vassocl.
              rewrite lwhisker_lwhisker.
              apply idpath.
            }
            rewrite !vassocl.
            etrans.
            {
              do 2 apply maponpaths.
              do 2 refine (vassocr _ _ _ @ _).
              apply maponpaths_2.
              rewrite <- vcomp_whisker.
              rewrite !vassocl.
              rewrite lwhisker_vcomp.
              rewrite vcomp_rinv.
              rewrite lwhisker_id2.
              apply id2_right.
            }
            apply idpath.
          }
          do 3 refine (vassocr _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths_2.
            rewrite !vassocl.
            rewrite lwhisker_vcomp.
            rewrite vcomp_linv.
            rewrite lwhisker_id2.
            apply id2_right.
          }
          rewrite rinvunitor_triangle.
          use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
          rewrite !vassocl.
          rewrite lassociator_rassociator.
          rewrite id2_right.
          rewrite rwhisker_rwhisker_alt.
          rewrite vcomp_whisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite vcomp_runitor.
            rewrite !vassocl.
            apply maponpaths.
            rewrite !vassocr.
            rewrite linvunitor_natural.
            rewrite <- lwhisker_hcomp.
            rewrite !vassocl.
            rewrite lwhisker_vcomp.
            rewrite vcomp_rinv.
            rewrite lwhisker_id2.
            apply id2_right.
          }
          rewrite !vassocr.
          rewrite rinvunitor_runitor.
          rewrite id2_left.
          rewrite linvunitor_assoc.
          apply idpath.
        + apply TODO.
      - intros b₁ b₂ f g τ ; cbn.
        use binprod_ump_2cell_unique_alt.
        + apply (pr2 B₂).
        + apply TODO.
        + apply TODO.
    Time Qed.

    Definition pstrans_pair
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : pstrans H binprod_psfunctor.
    Proof.
      use make_pstrans.
      - exact (pstrans_pair_data α β).
      - exact (pstrans_pair_is_pstrans α β).
    Defined.

    Definition pstrans_pair_pr1_data
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : invertible_modification_data
          (comp_pstrans
             (pstrans_pair α β)
             binprod_psfunctor_pr1)
          α
      := λ x, prod_1cell_pr1 _ (α x) (β x).

    Definition pstrans_pair_pr1_is_modification
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : is_modification (pstrans_pair_pr1_data α β).
    Proof.
      intros x y f.
      simpl.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply prod_2cell_pr1.
        }
        apply maponpaths.
        apply maponpaths_2.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocl.
      etrans.
      {
        do 11 apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply lassociator_rassociator.
        }
        apply id2_left.
      }
      etrans.
      {
        do 9 apply maponpaths.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_right.
      }
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_left.
      }
      apply rassociator_lassociator.
    Qed.

    Definition pstrans_pair_pr1
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : invertible_modification
          (comp_pstrans
             (pstrans_pair α β)
             binprod_psfunctor_pr1)
          α.
    Proof.
      use make_invertible_modification.
      - exact (pstrans_pair_pr1_data α β).
      - exact (pstrans_pair_pr1_is_modification α β).
    Defined.

    Definition pstrans_pair_pr2_data
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : invertible_modification_data
          (comp_pstrans
             (pstrans_pair α β)
             binprod_psfunctor_pr2)
          β
      := λ x, prod_1cell_pr2 _ (α x) (β x).

    Definition pstrans_pair_pr2_is_modification
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : is_modification (pstrans_pair_pr2_data α β).
    Proof.
      intros x y f.
      simpl.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply prod_2cell_pr2.
        }
        apply maponpaths.
        apply maponpaths_2.
        apply binprod_ump_2cell_pr2.
      }
      rewrite !vassocl.
      etrans.
      {
        do 11 apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          apply lassociator_rassociator.
        }
        apply id2_left.
      }
      etrans.
      {
        do 9 apply maponpaths.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_right.
      }
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        apply binprod_ump_2cell_pr2.
      }
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_left.
      }
      apply rassociator_lassociator.
    Qed.

    Definition pstrans_pair_pr2
               {H : psfunctor B₁ B₂}
               (α : pstrans H F)
               (β : pstrans H G)
      : invertible_modification
          (comp_pstrans
             (pstrans_pair α β)
             binprod_psfunctor_pr2)
          β.
    Proof.
      use make_invertible_modification.
      - exact (pstrans_pair_pr2_data α β).
      - exact (pstrans_pair_pr2_is_modification α β).
    Defined.

    Definition prod_modification_data
               {H : psfunctor B₁ B₂}
               {α β : pstrans H binprod_psfunctor}
               (m : modification
                      (α · binprod_cone_pr1 psfunctor_binprod_cone)
                      (β · binprod_cone_pr1 psfunctor_binprod_cone))
               (n : modification
                      (α · binprod_cone_pr2 psfunctor_binprod_cone)
                      (β · binprod_cone_pr2 psfunctor_binprod_cone))
      : modification_data α β.
    Proof.
      intro x.
      use binprod_ump_2cell.
      - apply (pr2 B₂).
      - exact (m x).
      - exact (n x).
    Defined.

    Definition prod_modification_is_modification
               {H : psfunctor B₁ B₂}
               {α β : pstrans H binprod_psfunctor}
               (m : modification
                      (α · binprod_cone_pr1 psfunctor_binprod_cone)
                      (β · binprod_cone_pr1 psfunctor_binprod_cone))
               (n : modification
                      (α · binprod_cone_pr2 psfunctor_binprod_cone)
                      (β · binprod_cone_pr2 psfunctor_binprod_cone))
      : is_modification (prod_modification_data m n).
    Proof.
      intros x y f.
      use binprod_ump_2cell_unique_alt.
      - apply (pr2 B₂).
      - unfold prod_modification_data.
        rewrite <- !rwhisker_vcomp.
        use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
        simpl.
        rewrite !vassocl.
        rewrite <- rwhisker_lwhisker_rassociator.
        etrans.
        {
          do 3 apply maponpaths.
          apply binprod_ump_2cell_pr1.
        }
        pose (q := modnaturality_of m _ _ f).
        simpl in q.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        use (vcomp_lcancel (_ ◃  (pair_1cell_pr1 B₂ (# F f) (# G f)) ^-1)) ; [ is_iso | ].
        use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
        rewrite !vassocr.
        refine (q @ _) ; clear q.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite rwhisker_rwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        etrans.
        {
          rewrite !vassocl.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite <- rwhisker_rwhisker_alt.
        apply maponpaths_2.
        apply maponpaths.
        apply binprod_ump_2cell_pr1.
      - unfold prod_modification_data.
        rewrite <- !rwhisker_vcomp.
        use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
        simpl.
        rewrite !vassocl.
        rewrite <- rwhisker_lwhisker_rassociator.
        etrans.
        {
          do 3 apply maponpaths.
          apply binprod_ump_2cell_pr2.
        }
        pose (q := modnaturality_of n _ _ f).
        simpl in q.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        use (vcomp_lcancel (_ ◃  (pair_1cell_pr2 B₂ (# F f) (# G f)) ^-1)) ; [ is_iso | ].
        use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
        rewrite !vassocr.
        refine (q @ _) ; clear q.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite rwhisker_rwhisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        etrans.
        {
          rewrite !vassocl.
          rewrite <- vcomp_whisker.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite <- rwhisker_rwhisker_alt.
        apply maponpaths_2.
        apply maponpaths.
        apply binprod_ump_2cell_pr2.
    Qed.

    Definition prod_modification
               {H : psfunctor B₁ B₂}
               {α β : pstrans H binprod_psfunctor}
               (m : modification
                      (α · binprod_cone_pr1 psfunctor_binprod_cone)
                      (β · binprod_cone_pr1 psfunctor_binprod_cone))
               (n : modification
                      (α · binprod_cone_pr2 psfunctor_binprod_cone)
                      (β · binprod_cone_pr2 psfunctor_binprod_cone))
      : modification α β.
    Proof.
      use make_modification.
      - exact (prod_modification_data m n).
      - exact (prod_modification_is_modification m n).
    Defined.

    Definition psfunctor_binprod_ump
      : has_binprod_ump psfunctor_binprod_cone.
    Proof.
      use make_binprod_ump.
      - intro q.
        use make_binprod_1cell.
        + exact (pstrans_pair (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
        + exact (pstrans_pair_pr1 (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
        + exact (pstrans_pair_pr2 (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
      - intros q α β m n.
        exact (prod_modification m n).
      - abstract
          (intros H α β m n ;
           use modification_eq ;
           intros x ;
           apply binprod_ump_2cell_pr1).
      - abstract
          (intros H α β m n ;
           use modification_eq ;
           intros x ;
           apply binprod_ump_2cell_pr2).
      - abstract
          (intro ; intros ;
           use modification_eq ;
           intros x ;
           pose (modcomponent_eq γpr1 x) as p₁ ;
           pose (modcomponent_eq γpr2 x) as p₂ ;
           pose (modcomponent_eq δpr1 x) as p₃ ;
           pose (modcomponent_eq δpr2 x) as p₄ ;
           use (binprod_ump_2cell_unique
                  _
                  (pr111 α x)
                  (pr111 β x)
                  _ _
                  p₁ p₂ p₃ p₄) ;
           apply (pr2 B₂)).
    Defined.
  End BinprodPSFunctor.

  Definition psfunctor_has_binprod
    : has_binprod (psfunctor_bicat B₁ B₂).
  Proof.
    intros F G.
    simple refine (_ ,, _).
    - exact (psfunctor_binprod_cone F G).
    - exact (psfunctor_binprod_ump F G).
  Defined.
End FixProducts.
 *)
