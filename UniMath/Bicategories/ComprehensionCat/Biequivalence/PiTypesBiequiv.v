(******************************************************************************************


 Contents
 1. The extended pseudofunctor from categories to comprehension categories
 2. The extended pseudofunctor from comprehension categories to categories
 3. The unit
 4. The counit
 5. The displayed biequivalence

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Lemmas on equivalences and locally cartesian closed categories *)
Proposition id_preserves_locally_cartesian_closed'
            {C : univalent_category}
            {PB₁ : Pullbacks C}
            {PB₂ : Pullbacks C}
            (FPB : preserves_pullback (functor_identity C))
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  assert (PB₁ = PB₂) as q.
  {
    apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  }
  induction q.
  assert (identity_preserves_pullback _ = FPB) as q.
  {
    apply isaprop_preserves_pullback.
  }
  induction q.
  assert (P₁ = P₂) as q.
  {
    apply isaprop_is_locally_cartesian_closed.
  }
  induction q.
  apply id_preserves_locally_cartesian_closed.
Qed.

Proposition preserves_locally_cartesian_closed_adj_equiv
            {C₁ C₂ : bicat_of_univ_cats}
            (F : adjoint_equivalence C₁ C₂)
            {PB₁ : Pullbacks (C₁ : univalent_category)}
            {PB₂ : Pullbacks (C₂ : univalent_category)}
            (FPB : preserves_pullback (pr1 F))
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  revert C₁ C₂ F PB₁ PB₂ FPB P₁ P₂.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C PB₁ PB₂ FPB P₁ P₂.
  apply id_preserves_locally_cartesian_closed'.
Qed.

Proposition preserves_locally_cartesian_closed_left_adjoint_equivalence
            {C₁ C₂ : univalent_category}
            (F : C₁ ⟶ C₂)
            (HF : left_adjoint_equivalence (B := bicat_of_univ_cats) F)
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  exact (preserves_locally_cartesian_closed_adj_equiv (F ,, HF) FPB P₁ P₂).
Qed.

Proposition preserves_locally_cartesian_closed_adj_equivalence_of_cats
            {C₁ C₂ : univalent_category}
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  refine (preserves_locally_cartesian_closed_left_adjoint_equivalence F _ FPB P₁ P₂).
  use equiv_cat_to_adj_equiv.
  exact HF.
Qed.

Proposition preserves_locally_cartesian_closed_adj_equivalence_of_cats'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  exact (preserves_locally_cartesian_closed_adj_equivalence_of_cats
           (C₁ := make_univalent_category C₁ HC₁)
           (C₂ := make_univalent_category C₂ HC₂)
           F
           HF
           FPB
           P₁ P₂).
Qed.

Proposition locally_cartesian_closed_adj_equiv_f_help
            {C₁ C₂ : bicat_of_univ_cats}
            (F : adjoint_equivalence C₁ C₂)
            {PB₁ : Pullbacks (C₁ : univalent_category)}
            {PB₂ : Pullbacks (C₂ : univalent_category)}
            (FPB : preserves_pullback (pr1 F))
            (P₁ : is_locally_cartesian_closed PB₁)
  : is_locally_cartesian_closed PB₂.
Proof.
  revert C₁ C₂ F PB₁ PB₂ FPB P₁.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C PB₁ PB₂ FPB P₁.
  assert (PB₁ = PB₂) as p.
  {
    apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  }
  rewrite <- p.
  exact P₁.
Qed.

Proposition locally_cartesian_closed_left_adjoint_equivalence_f
            {C₁ C₂ : bicat_of_univ_cats}
            (F : bicat_of_univ_cats ⟦ C₁ , C₂ ⟧)
            (HF : left_adjoint_equivalence F)
            {PB₁ : Pullbacks (C₁ : univalent_category)}
            {PB₂ : Pullbacks (C₂ : univalent_category)}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
  : is_locally_cartesian_closed PB₂.
Proof.
  exact (locally_cartesian_closed_adj_equiv_f_help (F ,, HF) FPB P₁).
Qed.

Proposition locally_cartesian_closed_adj_equiv_f
            {C₁ C₂ : univalent_category}
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
  : is_locally_cartesian_closed PB₂.
Proof.
  refine (locally_cartesian_closed_left_adjoint_equivalence_f F _ FPB P₁).
  use equiv_cat_to_adj_equiv.
  exact HF.
Qed.

Proposition locally_cartesian_closed_adj_equiv_f'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (FPB : preserves_pullback F)
            (P₁ : is_locally_cartesian_closed PB₁)
  : is_locally_cartesian_closed PB₂.
Proof.
  exact (@locally_cartesian_closed_adj_equiv_f
           (make_univalent_category C₁ HC₁)
           (make_univalent_category C₂ HC₂)
           F HF
           _ _
           FPB
           P₁).
Qed.

Proposition preserves_locally_cartesian_closed_nat_z_iso_f_help
            {C₁ C₂ : bicat_of_univ_cats}
            {PB₁ : Pullbacks (C₁ : univalent_category)}
            {PB₂ : Pullbacks (C₂ : univalent_category)}
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
            {F G : C₁ --> C₂}
            {FPB : preserves_pullback F}
            (GPB : preserves_pullback G)
            (HF : preserves_locally_cartesian_closed FPB P₁ P₂)
            (τ : invertible_2cell F G)
  : preserves_locally_cartesian_closed GPB P₁ P₂.
Proof.
  revert C₁ C₂ F G τ PB₁ PB₂ P₁ P₂ FPB GPB HF.
  use J_2_1.
  {
    exact univalent_cat_is_univalent_2_1.
  }
  intros C₁ C₂ F PB₁ PB₂ P₁ P₂ FPB GPB HF.
  assert (FPB = GPB) as q.
  {
    apply isaprop_preserves_pullback.
  }
  induction q.
  exact HF.
Qed.

Proposition preserves_locally_cartesian_closed_nat_z_iso_f
            {C₁ C₂ : univalent_category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
            {F G : C₁ ⟶ C₂}
            {FPB : preserves_pullback F}
            (GPB : preserves_pullback G)
            (HF : preserves_locally_cartesian_closed FPB P₁ P₂)
            (τ : nat_z_iso F G)
  : preserves_locally_cartesian_closed GPB P₁ P₂.
Proof.
  refine (preserves_locally_cartesian_closed_nat_z_iso_f_help P₁ P₂ GPB HF _).
  use nat_z_iso_to_invertible_2cell.
  exact τ.
Qed.

Proposition preserves_locally_cartesian_closed_nat_z_iso_adj_equiv_f_help
            {C₁ C₂ D₁ D₂ : bicat_of_univ_cats}
            {PBC₁ : Pullbacks (C₁ : univalent_category)}
            {PBC₂ : Pullbacks (C₂ : univalent_category)}
            {PBD₁ : Pullbacks (D₁ : univalent_category)}
            {PBD₂ : Pullbacks (D₂ : univalent_category)}
            (PC₁ : is_locally_cartesian_closed PBC₁)
            (PC₂ : is_locally_cartesian_closed PBC₂)
            (PD₁ : is_locally_cartesian_closed PBD₁)
            (PD₂ : is_locally_cartesian_closed PBD₂)
            (EC : adjoint_equivalence C₁ C₂)
            (ED : adjoint_equivalence D₁ D₂)
            {F : C₁ --> D₁}
            {FPB : preserves_pullback F}
            {G : C₂ --> D₂}
            {GPB : preserves_pullback G}
            (τ : nat_z_iso (F ∙ pr1 ED) (pr1 EC ∙ G))
            (HF : preserves_locally_cartesian_closed FPB PC₁ PD₁)
  : preserves_locally_cartesian_closed GPB PC₂ PD₂.
Proof.
  revert C₁ C₂ EC D₁ D₂ ED PBC₁ PBC₂ PBD₁ PBD₂ PC₁ PC₂ PD₁ PD₂ F FPB G GPB τ HF.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros D PBC₁ PBC₂ PBD₁ PBD₂ PC₁ PC₂ PD₁ PD₂ F FPB G GPB τ HF.
  assert (PBC₁ = PBC₂) as q.
  {
    apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  }
  induction q.
  assert (PBD₁ = PBD₂) as q.
  {
    apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  }
  induction q.
  assert (PC₁ = PC₂) as q.
  {
    apply isaprop_is_locally_cartesian_closed.
  }
  induction q.
  assert (PD₁ = PD₂) as q.
  {
    apply isaprop_is_locally_cartesian_closed.
  }
  induction q.
  exact (preserves_locally_cartesian_closed_nat_z_iso_f PC₁ PD₁ GPB HF τ).
Qed.

Proposition preserves_locally_cartesian_closed_nat_z_iso_adj_equiv_f
            {C₁ C₂ D₁ D₂ : univalent_category}
            {PBC₁ : Pullbacks C₁}
            {PBC₂ : Pullbacks C₂}
            {PBD₁ : Pullbacks D₁}
            {PBD₂ : Pullbacks D₂}
            (PC₁ : is_locally_cartesian_closed PBC₁)
            (PC₂ : is_locally_cartesian_closed PBC₂)
            (PD₁ : is_locally_cartesian_closed PBD₁)
            (PD₂ : is_locally_cartesian_closed PBD₂)
            {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
            (HEC : adj_equivalence_of_cats EC)
            (HED : adj_equivalence_of_cats ED)
            {F : C₁ ⟶ D₁}
            {FPB : preserves_pullback F}
            {G : C₂ ⟶ D₂}
            {GPB : preserves_pullback G}
            (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
            (HF : preserves_locally_cartesian_closed FPB PC₁ PD₁)
  : preserves_locally_cartesian_closed GPB PC₂ PD₂.
Proof.
  refine (preserves_locally_cartesian_closed_nat_z_iso_adj_equiv_f_help
            PC₁ PC₂ PD₁ PD₂
            (EC ,, _) (ED ,, _)
            τ
            HF).
  - use equiv_cat_to_adj_equiv.
    exact HEC.
  - use equiv_cat_to_adj_equiv.
    exact HED.
Qed.

Proposition preserves_locally_cartesian_closed_nat_z_iso_adj_equiv_f'
            {C₁ C₂ D₁ D₂ : category}
            (HC₁' : is_univalent C₁)
            (HC₂' : is_univalent C₂)
            (HD₁' : is_univalent D₁)
            (HD₂' : is_univalent D₂)
            {PBC₁ : Pullbacks C₁}
            {PBC₂ : Pullbacks C₂}
            {PBD₁ : Pullbacks D₁}
            {PBD₂ : Pullbacks D₂}
            (PC₁ : is_locally_cartesian_closed PBC₁)
            (PC₂ : is_locally_cartesian_closed PBC₂)
            (PD₁ : is_locally_cartesian_closed PBD₁)
            (PD₂ : is_locally_cartesian_closed PBD₂)
            {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
            (HEC : adj_equivalence_of_cats EC)
            (HED : adj_equivalence_of_cats ED)
            {F : C₁ ⟶ D₁}
            {FPB : preserves_pullback F}
            {G : C₂ ⟶ D₂}
            {GPB : preserves_pullback G}
            (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
            (HF : preserves_locally_cartesian_closed FPB PC₁ PD₁)
  : preserves_locally_cartesian_closed GPB PC₂ PD₂.
Proof.
  exact (preserves_locally_cartesian_closed_nat_z_iso_adj_equiv_f
           (C₁ := make_univalent_category C₁ HC₁')
           (C₂ := make_univalent_category C₂ HC₂')
           (D₁ := make_univalent_category D₁ HD₁')
           (D₂ := make_univalent_category D₂ HD₂')
           PC₁ PC₂ PD₁ PD₂
           HEC HED
           τ
           HF).
Qed.

(** * 1. The extended pseudofunctor from categories to comprehension categories *)
Definition finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_univ_lccc
      disp_bicat_of_pi_type_dfl_full_comp_cat
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, _ ,, tt).
    apply cod_dependent_products.
    exact (pr1 H).
  - refine (λ C₁ C₂ F P₁ P₂ HF, _).
    exact HF.
Defined.

(** * 2. The extended pseudofunctor from comprehension categories to categories *)
Definition dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_of_pi_type_dfl_full_comp_cat
      disp_bicat_univ_lccc
      dfl_comp_cat_to_finlim_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - refine (λ C P, _ ,, tt).
    (*
    cbn.
    unfold is_locally_cartesian_closed.
    intros x y f.
    pose (pr11 P x y f) as q.
    unfold dependent_product in q.
     *)
    cbn.
    unfold is_locally_cartesian_closed.
    (* *)
    admit.
  - intros C₁ C₂ F P₁ P₂ HF.
    refine (tt ,, _).
    cbn.
    unfold preserves_locally_cartesian_closed.
    pose (pr2 HF) as q.
    cbn in q.
Admitted.

(** * 3. The unit *)
Definition finlim_dfl_comp_cat_unit_pi_types
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_unit.
Proof.
  use make_disp_pstrans_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - intros C H.
    refine (tt ,, _).
    apply id_preserves_locally_cartesian_closed'.
Qed.

Definition finlim_dfl_comp_cat_unit_pi_types_pointwise_adjequiv
           {C : univ_cat_with_finlim}
           (HC : disp_bicat_univ_lccc C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_unit_pointwise_equiv C)
      (finlim_dfl_comp_cat_unit_pi_types C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_univ_lccc.
Qed.

Definition finlim_dfl_comp_cat_unit_inv_pi_types
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types)
      finlim_dfl_comp_cat_unit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - apply finlim_dfl_comp_cat_unit_pi_types.
  - intros.
    apply finlim_dfl_comp_cat_unit_pi_types_pointwise_adjequiv.
Qed.

(** * 4. The counit *)
Definition finlim_dfl_comp_cat_counit_pi_types
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types)
      finlim_dfl_comp_cat_counit.
Proof.
  use make_disp_pstrans_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, tt ,, _).
    cbn.
    Check preserves_locally_cartesian_closed_adj_equivalence_of_cats'.
    use (preserves_locally_cartesian_closed_adj_equivalence_of_cats'
              _ _
              _
              (fiber_functor_comprehension_adj_equiv C x)).
    (*intro x ; cbn.
    use (cat_property_adj_equivalence_of_cats'
           P
           _ _ _
           (fiber_functor_comprehension_adj_equiv C x)).
    + apply is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    + apply is_univalent_fiber.
      apply disp_univalent_disp_codomain.
Qed.
     *)
Admitted.

Definition finlim_dfl_comp_cat_counit_pi_types_pointwise_adjequiv
           {C : dfl_full_comp_cat}
           (HC : disp_bicat_of_pi_type_dfl_full_comp_cat C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_counit_pointwise_equiv C)
      (finlim_dfl_comp_cat_counit_pi_types C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat.
Qed.

Definition finlim_dfl_comp_cat_counit_inv_pi_types
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_counit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply finlim_dfl_comp_cat_counit_pi_types.
  - intros.
    apply finlim_dfl_comp_cat_counit_pi_types_pointwise_adjequiv.
Qed.

(** * 5. The displayed biequivalence *)
Definition finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types
  : is_disp_biequivalence_unit_counit
      _ _
      finlim_dfl_comp_cat_biequivalence_unit_counit
      finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
      dfl_comp_cat_to_finlim_disp_psfunctor_pi_types.
Proof.
  simple refine (_ ,, _).
  - exact finlim_dfl_comp_cat_unit_pi_types.
  - exact finlim_dfl_comp_cat_counit_inv_pi_types.
Defined.

Definition finlim_biequiv_dfl_comp_cat_psfunctor_local_property
  : disp_is_biequivalence_data
      _
      _
      finlim_dfl_comp_cat_biequivalence_adjoints
      finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types.
Proof.
  simple refine (_ ,, _ ,, (_ ,, _) ,, (_ ,, _)).
  - exact finlim_dfl_comp_cat_unit_inv_pi_types.
  - exact finlim_dfl_comp_cat_counit_pi_types.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_univ_lccc.
    + exact disp_locally_groupoid_univ_lccc.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_univ_lccc.
    + exact disp_locally_groupoid_univ_lccc.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.
