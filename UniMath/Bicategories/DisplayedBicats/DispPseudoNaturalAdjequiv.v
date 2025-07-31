(**

 Displayed pseudonatural adjoint equivalences

 A convenient way to check that a pseudonatural transformation is an adjoint equivalence,
 is by checking that it is an adjoint equivalence at every point. This means that we do
 not have to check any pseudonaturality conditions and that we do not have to construct
 any invertible modification. In this file, we prove an analogous statement for displayed
 pseudotransformations.

 We make some simplifying assumptions in the development. We have displayed pseudofunctors
 `FF₁ FF₂ : D₁ -->[ F ] D₂` and a displayed pseudotransformation `ττ : FF₁ ==>[ τ ] FF₂`,
 and our simplifying assumptions say that all 2-cells in `D₂` are equal and invertible.
 These assumptions are made to trivialize the coherences that are necessary to prove. We
 also assume that the bicategory `B₂` over which `D₂` lives. is univalent. This allows us
 to use equivalence induction, meaning that we can assume that our displayed
 pseudotransformation lives over the identity, which further simplifies the development.

 We conclude this file by giving a convenient constructor for displayed biequivalences.

 Contents
 1. Displaued pseudonatural adjoint equivalences over the identity
 2. Displayed pseudonatural adjoint equivalences over arbitrary morphisms
 3. A convenient builder for displayed biequivalences
                                                                                       *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
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
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.

Local Open Scope cat.

(** * 1. Displaued pseudonatural adjoint equivalences over the identity *)
Section DispPseudoNaturalAdjointEquivalenceId.
  Context {B₁ B₂ : bicat}
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (Dprop₂ : disp_2cells_isaprop D₂)
          (Dgrpd₂ : disp_locally_groupoid D₂)
          {F : psfunctor B₁ B₂}
          {FF₁ : disp_psfunctor D₁ D₂ F}
          {FF₂ : disp_psfunctor D₁ D₂ F}
          (ττ : disp_pstrans FF₁ FF₂ (identity _))
          (Hττ : ∏ (x : B₁)
                   (xx : D₁ x),
                 disp_left_adjoint_equivalence
                   (internal_adjoint_equivalence_identity _)
                   (ττ x xx)).

  Lemma inv_disp_left_adjoint_equivalence_lem
        {x y : B₁}
        (f : x --> y)
    : rinvunitor _
      • (_ ◃ linvunitor _)
      • rassociator _ _ _
      • (_ ◃ lassociator _ _ _)
      • (_ ◃ ((runitor _ • linvunitor _) ▹ _))
      • lassociator _ _ _
      • ((lassociator _ _ _
          • (lunitor _ ▹ _)
          • lunitor _) ▹ _)
      =
      lunitor _
      • rinvunitor (#F f).
  Proof.
    etrans.
    {
      do 4 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    rewrite !vassocl.
    rewrite <- vcomp_lunitor.
    apply maponpaths.
    rewrite <- lunitor_triangle.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    etrans.
    {
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite pentagon_6.
      apply idpath.
    }
    rewrite !vassocl.
    rewrite rwhisker_rwhisker.
    rewrite !vassocr.
    refine (_ @ id2_left _).
    apply maponpaths_2.
    rewrite lwhisker_vcomp.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_V_id_is_left_unit_V_id.
      rewrite rinvunitor_triangle.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ].
    cbn.
    rewrite id2_left.
    rewrite <- lunitor_triangle.
    refine (_ @ id2_right _).
    rewrite !vassocl.
    apply maponpaths.
    rewrite !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite rwhisker_hcomp.
    rewrite rinvunitor_natural.
    rewrite <- !rwhisker_hcomp.
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite !vassocr.
    rewrite vcomp_runitor.
    rewrite !vassocl.
    rewrite lunitor_linvunitor.
    rewrite id2_right.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    apply runitor_rinvunitor.
  Qed.

  Definition pointwise_disp_adjequiv_to_adjequiv_id
    : disp_pstrans FF₂ FF₁ (identity _).
  Proof.
    use make_disp_pstrans.
    - exact Dprop₂.
    - exact Dgrpd₂.
    - intros x xx.
      apply (Hττ x xx).
    - abstract
        (intros x y f xx yy ff ;
         exact (transportf
                  (λ z, _ ==>[ z ] _)
                  (inv_disp_left_adjoint_equivalence_lem f)
                  (disp_rinvunitor _
                   •• (_ ◃◃ pr121 (Hττ y yy))
                   •• disp_rassociator _ _ _
                   •• (_ ◃◃ disp_lassociator _ _ _)
                   •• (_ ◃◃ (disp_inv_cell (disp_psnaturality_of _ _ _ ττ ff) ▹▹ _))
                   •• disp_lassociator _ _ _
                   •• ((disp_lassociator _ _ _
                       •• (pr221 (Hττ x xx) ▹▹ _)
                       •• disp_lunitor _) ▹▹ _)))).
  Defined.

  Definition pointwise_disp_adjequiv_to_adjequiv_id_pointwise_adjequiv
             {x : B₁}
             (xx : D₁ x)
    : disp_left_adjoint_equivalence
        (internal_adjoint_equivalence_identity _)
        (pointwise_disp_adjequiv_to_adjequiv_id x xx).
  Proof.
    simple refine (_ ,, _).
    - simple refine (_ ,, _ ,, _).
      + exact (ττ x xx).
      + apply Hττ.
      + apply Hττ.
    - split.
      + split ; apply Dprop₂.
      + split ; apply Dgrpd₂.
  Qed.

  Definition pointwise_disp_adjequiv_to_adjequiv_id_left
    : disp_invmodification
        _ _ _ _
        (disp_comp_pstrans
           ττ
           pointwise_disp_adjequiv_to_adjequiv_id)
        (disp_id_pstrans _)
        (lunitor_invertible_2cell _).
  Proof.
    use make_disp_invmodification.
    - exact Dprop₂.
    - exact Dgrpd₂.
    - intros x xx ; cbn.
      apply Hττ.
  Qed.

  Definition pointwise_disp_adjequiv_to_adjequiv_id_right
    : disp_invmodification
        _ _ _ _
        (disp_comp_pstrans
           pointwise_disp_adjequiv_to_adjequiv_id
           ττ)
        (disp_id_pstrans _)
        (lunitor_invertible_2cell _).
  Proof.
    use make_disp_invmodification.
    - exact Dprop₂.
    - exact Dgrpd₂.
    - intros x xx ; cbn.
      exact (pr221 (Hττ x xx)).
  Qed.
End DispPseudoNaturalAdjointEquivalenceId.

(** * 2. Displayed pseudonatural adjoint equivalences over arbitrary morphisms *)
Lemma pointwise_disp_adjequiv_to_adjequiv_help_eq
      {B₁ B₂ : bicat}
      {D₁ : disp_bicat B₁}
      {D₂ : disp_bicat B₂}
      {F : psfunctor B₁ B₂}
      {FF₁ FF₂ : disp_psfunctor D₁ D₂ F}
      {ττ : disp_pstrans FF₁ FF₂ (identity F)}
      (Hττ : ∏ (x : B₁)
               (xx : D₁ x),
             disp_left_adjoint_equivalence
               (pointwise_adjequiv
                  (pr1 (internal_adjoint_equivalence_identity F))
                  (pr2 (internal_adjoint_equivalence_identity F)) x)
               (ττ x xx))
      (x : B₁)
      (xx : D₁ x)
  : disp_left_adjoint_equivalence
      (internal_adjoint_equivalence_identity (F x))
      (ττ x xx).
Proof.
  specialize (Hττ x xx).
  refine (transportf
            (λ z, disp_left_adjoint_equivalence z (ττ x xx))
            _
            Hττ).
  use subtypePath.
  {
    intro.
    repeat use isapropdirprod ;
      try apply cellset_property ;
      apply isaprop_is_invertible_2cell.
  }
  apply idpath.
Qed.

Definition pointwise_disp_adjequiv_to_adjequiv_help
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : adjoint_equivalence F G}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG (pr1 τ))
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv (pr1 τ) (pr2 τ) x)
                 (ττ x xx))
  : disp_pstrans GG FF (left_adjoint_right_adjoint τ).
Proof.
  revert F G τ FF GG ττ Hττ.
  use J_2_0.
  {
    use psfunctor_bicat_is_univalent_2_0.
    exact HB₂.
  }
  intros F FF₁ FF₂ ττ Hττ.
  use pointwise_disp_adjequiv_to_adjequiv_id.
  - exact Dprop₂.
  - exact Dgrpd₂.
  - exact ττ.
  - apply pointwise_disp_adjequiv_to_adjequiv_help_eq.
    exact Hττ.
Defined.

Definition pointwise_disp_adjequiv_to_adjequiv_help_pointwise_adjequiv
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : adjoint_equivalence F G}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG (pr1 τ))
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv (pr1 τ) (pr2 τ) x)
                 (ττ x xx))
           {x : B₁}
           (xx : D₁ x)
  : disp_left_adjoint_equivalence
      (inv_left_adjoint_equivalence
         (pointwise_adjequiv (pr1 τ) (pr2 τ) x))
      (pointwise_disp_adjequiv_to_adjequiv_help
         HB₂ Dprop₂ Dgrpd₂ ττ Hττ
         x xx).
Proof.
  revert F G τ FF GG ττ Hττ.
  use J_2_0.
  {
    use psfunctor_bicat_is_univalent_2_0.
    exact HB₂.
  }
  intros F FF₁ FF₂ ττ Hττ.
  unfold pointwise_disp_adjequiv_to_adjequiv_help.
  rewrite J_2_0_comp.
  assert (inv_left_adjoint_equivalence
            (pointwise_adjequiv
               (pr1 (internal_adjoint_equivalence_identity F))
               (pr2 (internal_adjoint_equivalence_identity F)) x)
          =
          internal_adjoint_equivalence_identity _)
    as ->.
  {
    apply (isaprop_left_adjoint_equivalence _ (pr2 HB₂)).
  }
  use pointwise_disp_adjequiv_to_adjequiv_id_pointwise_adjequiv.
Qed.

Definition pointwise_disp_adjequiv_to_adjequiv_left_help
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : adjoint_equivalence F G}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG (pr1 τ))
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv (pr1 τ) (pr2 τ) x)
                 (ττ x xx))
  : disp_invmodification
      _ _ _ _
      (disp_comp_pstrans
         ττ
         (pointwise_disp_adjequiv_to_adjequiv_help HB₂ Dprop₂ Dgrpd₂ ττ Hττ))
      (disp_id_pstrans _)
      (inv_of_invertible_2cell (left_equivalence_unit_iso τ)).
Proof.
  revert F G τ FF GG ττ Hττ.
  use J_2_0.
  {
    use psfunctor_bicat_is_univalent_2_0.
    exact HB₂.
  }
  intros F FF₁ FF₂ ττ Hττ.
  use make_disp_invmodification.
  - exact Dprop₂.
  - exact Dgrpd₂.
  - intros x xx.
    unfold pointwise_disp_adjequiv_to_adjequiv_help.
    rewrite J_2_0_comp.
    simpl ; cbn.
    pose (pr1 (pr1 (pointwise_disp_adjequiv_to_adjequiv_id_left
                      Dprop₂ Dgrpd₂ ττ
                      (pointwise_disp_adjequiv_to_adjequiv_help_eq Hττ))
                 x xx)).
    simpl in d ; cbn in d.
    exact d.
Qed.

Definition pointwise_disp_adjequiv_to_adjequiv_right_help
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : adjoint_equivalence F G}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG (pr1 τ))
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv (pr1 τ) (pr2 τ) x)
                 (ττ x xx))
  : disp_invmodification
      _ _ _ _
      (disp_comp_pstrans
         (pointwise_disp_adjequiv_to_adjequiv_help HB₂ Dprop₂ Dgrpd₂ ττ Hττ)
         ττ)
      (disp_id_pstrans _)
      (left_equivalence_counit_iso τ).
Proof.
  revert F G τ FF GG ττ Hττ.
  use J_2_0.
  {
    use psfunctor_bicat_is_univalent_2_0.
    exact HB₂.
  }
  intros F FF₁ FF₂ ττ Hττ.
  use make_disp_invmodification.
  - exact Dprop₂.
  - exact Dgrpd₂.
  - intros x xx.
    unfold pointwise_disp_adjequiv_to_adjequiv_help.
    rewrite J_2_0_comp.
    exact (pr1 (pointwise_disp_adjequiv_to_adjequiv_id_right
                  Dprop₂ Dgrpd₂ ττ
                  (pointwise_disp_adjequiv_to_adjequiv_help_eq Hττ))
             x xx).
Qed.

Definition pointwise_disp_adjequiv_to_adjequiv
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : pstrans F G}
           (Hτ : left_adjoint_equivalence τ)
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG τ)
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv τ Hτ x)
                 (ττ x xx))
  : disp_pstrans GG FF (left_adjoint_right_adjoint Hτ).
Proof.
  exact (pointwise_disp_adjequiv_to_adjequiv_help
           HB₂ Dprop₂ Dgrpd₂
           (τ := τ ,, Hτ)
           ττ
           Hττ).
Defined.

Definition pointwise_disp_adjequiv_to_adjequiv_pointwise_adjequiv
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : pstrans F G}
           (Hτ : left_adjoint_equivalence τ)
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG τ)
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv τ Hτ x)
                 (ττ x xx))
           {x : B₁}
           (xx : D₁ x)
  : disp_left_adjoint_equivalence
      (inv_left_adjoint_equivalence
         (pointwise_adjequiv τ Hτ x))
      (pointwise_disp_adjequiv_to_adjequiv
         HB₂ Dprop₂ Dgrpd₂ Hτ ττ Hττ
         x xx).
Proof.
  exact (pointwise_disp_adjequiv_to_adjequiv_help_pointwise_adjequiv
           HB₂ Dprop₂ Dgrpd₂
           (τ := τ ,, Hτ)
           ττ
           Hττ
           xx).
Qed.

Definition pointwise_disp_adjequiv_to_adjequiv_left
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : pstrans F G}
           (Hτ : left_adjoint_equivalence τ)
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG τ)
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv τ Hτ x)
                 (ττ x xx))
  : disp_invmodification
      _ _ _ _
      (disp_comp_pstrans
         ττ
         (pointwise_disp_adjequiv_to_adjequiv HB₂ Dprop₂ Dgrpd₂ Hτ ττ Hττ))
      (disp_id_pstrans _)
      (inv_of_invertible_2cell (left_equivalence_unit_iso Hτ)).
Proof.
  exact (pointwise_disp_adjequiv_to_adjequiv_left_help
           HB₂ Dprop₂ Dgrpd₂
           (τ := τ ,, Hτ)
           ττ
           Hττ).
Defined.

Definition pointwise_disp_adjequiv_to_adjequiv_right
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2 B₂)
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (Dprop₂ : disp_2cells_isaprop D₂)
           (Dgrpd₂ : disp_locally_groupoid D₂)
           {F G : psfunctor B₁ B₂}
           {τ : pstrans F G}
           (Hτ : left_adjoint_equivalence τ)
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₁ D₂ G}
           (ττ : disp_pstrans FF GG τ)
           (Hττ : ∏ (x : B₁)
                    (xx : D₁ x),
               disp_left_adjoint_equivalence
                 (pointwise_adjequiv τ Hτ x)
                 (ττ x xx))
  : disp_invmodification
      _ _ _ _
      (disp_comp_pstrans
         (pointwise_disp_adjequiv_to_adjequiv HB₂ Dprop₂ Dgrpd₂ Hτ ττ Hττ)
         ττ)
      (disp_id_pstrans _)
      (left_equivalence_counit_iso Hτ).
Proof.
  exact (pointwise_disp_adjequiv_to_adjequiv_right_help
           HB₂ Dprop₂ Dgrpd₂
           (τ := τ ,, Hτ)
           ττ
           Hττ).
Defined.

(** * 3. A convenient builder for displayed biequivalences *)
Section DispBiequivBuilder.
  Context {B₁ B₂ : bicat}
          (HB₁ : is_univalent_2 B₁)
          (HB₂ : is_univalent_2 B₂)
          {F : psfunctor B₁ B₂}
          {G : psfunctor B₂ B₁}
          {e : is_biequivalence_unit_counit F G}
          (a : is_biequivalence_adjoints e)
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (Dprop₁ : disp_2cells_isaprop D₁)
          (Dgrpd₁ : disp_locally_groupoid D₁)
          (Dprop₂ : disp_2cells_isaprop D₂)
          (Dgrpd₂ : disp_locally_groupoid D₂)
          {FF : disp_psfunctor D₁ D₂ F}
          {GG : disp_psfunctor D₂ D₁ G}
          (ηη : disp_pstrans
                  (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                  (disp_pseudo_id D₁)
                  (unit_of_is_biequivalence e))
          (εε : disp_pstrans
                  (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                  (disp_pseudo_id D₂)
                  (counit_of_is_biequivalence e))
          (Hηη : ∏ (x : B₁)
                   (xx : D₁ x),
                 disp_left_adjoint_equivalence
                   (pointwise_adjequiv
                      (unit_of_is_biequivalence e)
                      (is_biequivalence_adjoint_unit a)
                      x)
                   (ηη x xx))
          (Hεε : ∏ (x : B₂)
                   (xx : D₂ x),
                 disp_left_adjoint_equivalence
                   (pointwise_adjequiv
                      (counit_of_is_biequivalence e)
                      (is_biequivalence_adjoint_counit a)
                      x)
                   (εε x xx)).

  Definition make_disp_biequiv_unit_counit_pointwise_adjequiv
    : is_disp_biequivalence_unit_counit D₁ D₂ e FF GG.
  Proof.
    repeat split.
    - exact ηη.
    - exact εε.
  Defined.

  Definition make_disp_biequiv_pointwise_adjequiv
    : disp_is_biequivalence_data
        D₁ D₂
        a
        make_disp_biequiv_unit_counit_pointwise_adjequiv.
  Proof.
    simple refine (_ ,, _ ,, (_ ,, _) ,, _ ,, _).
    - use pointwise_disp_adjequiv_to_adjequiv.
      + exact HB₁.
      + exact Dprop₁.
      + exact Dgrpd₁.
      + exact ηη.
      + exact Hηη.
    - use pointwise_disp_adjequiv_to_adjequiv.
      + exact HB₂.
      + exact Dprop₂.
      + exact Dgrpd₂.
      + exact εε.
      + exact Hεε.
    - use pointwise_disp_adjequiv_to_adjequiv_right.
    - use pointwise_disp_adjequiv_to_adjequiv_left.
    - use pointwise_disp_adjequiv_to_adjequiv_right.
    - use pointwise_disp_adjequiv_to_adjequiv_left.
  Defined.
End DispBiequivBuilder.

Section DispBiequivBuilder.
  Context {B₁ B₂ : bicat}
          (HB₁ : is_univalent_2 B₁)
          (HB₂ : is_univalent_2 B₂)
          {F : psfunctor B₁ B₂}
          {G : psfunctor B₂ B₁}
          {e : is_biequivalence_unit_counit F G}
          (a : is_biequivalence_adjoints e)
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (Dprop₁ : disp_2cells_isaprop D₁)
          (Dgrpd₁ : disp_locally_groupoid D₁)
          (Dprop₂ : disp_2cells_isaprop D₂)
          (Dgrpd₂ : disp_locally_groupoid D₂)
          {FF : disp_psfunctor D₁ D₂ F}
          {GG : disp_psfunctor D₂ D₁ G}
          (ηη : disp_pstrans
                  (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                  (disp_pseudo_id D₁)
                  (unit_of_is_biequivalence e))
          (εε : disp_pstrans
                  (disp_pseudo_id D₂)
                  (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                  (invcounit_of_is_biequivalence a))
          (Hηη : ∏ (x : B₁)
                   (xx : D₁ x),
                 disp_left_adjoint_equivalence
                   (pointwise_adjequiv
                      (unit_of_is_biequivalence e)
                      (is_biequivalence_adjoint_unit a)
                      x)
                   (ηη x xx))
          (Hεε : ∏ (x : B₂)
                   (xx : D₂ x),
                 disp_left_adjoint_equivalence
                   (pointwise_adjequiv
                      (invcounit_of_is_biequivalence a)
                      (inv_left_adjoint_equivalence
                         (is_biequivalence_adjoint_counit a))
                      x)
                   (εε x xx)).

  Let εε' : disp_pstrans
              (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
              (disp_pseudo_id D₂)
              (counit_of_is_biequivalence e)
    := pointwise_disp_adjequiv_to_adjequiv HB₂ Dprop₂ Dgrpd₂ _ εε Hεε.

  Definition make_disp_biequiv_unit_counit_pointwise_adjequiv_alt
    : is_disp_biequivalence_unit_counit D₁ D₂ e FF GG.
  Proof.
    repeat split.
    - exact ηη.
    - exact εε'.
  Defined.

  Definition make_disp_biequiv_pointwise_adjequiv_alt
    : disp_is_biequivalence_data
        D₁ D₂
        a
        make_disp_biequiv_unit_counit_pointwise_adjequiv_alt.
  Proof.
    simple refine (_ ,, _ ,, (_ ,, _) ,, _ ,, _).
    - use pointwise_disp_adjequiv_to_adjequiv.
      + exact HB₁.
      + exact Dprop₁.
      + exact Dgrpd₁.
      + exact ηη.
      + exact Hηη.
    - use pointwise_disp_adjequiv_to_adjequiv.
      + exact HB₂.
      + exact Dprop₂.
      + exact Dgrpd₂.
      + exact εε'.
      + abstract
          (intros x xx ;
           refine (transportf
                     (λ z, disp_left_adjoint_equivalence z _)
                     _
                     (pointwise_disp_adjequiv_to_adjequiv_pointwise_adjequiv
                        HB₂ Dprop₂ Dgrpd₂ _ εε Hεε
                        xx)) ;
           apply (isaprop_left_adjoint_equivalence _ (pr2 HB₂))).
    - use pointwise_disp_adjequiv_to_adjequiv_right.
    - use pointwise_disp_adjequiv_to_adjequiv_left.
    - use pointwise_disp_adjequiv_to_adjequiv_right.
    - use (pointwise_disp_adjequiv_to_adjequiv_left HB₂ Dprop₂ Dgrpd₂ _ εε'  _).
  Defined.
End DispBiequivBuilder.
