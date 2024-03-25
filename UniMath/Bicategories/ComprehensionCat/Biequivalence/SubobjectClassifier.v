(******************************************************************************************

 The biequivalence for subobject classifier types

 In this file, we extend the biequivalence by Clairambault and Dybjer to subobject classifier
 types. Subobject classifier types represent a universe of propositions, and one can interpret
 them in categories with finite limits and a subobject classifier. Examples of such categories
 are given by toposes, such as sets or presheaf categories.

 This biequivalence is constructed in very much the same way as the biequivalence for local
 properties (e.g., extensiveness, regularity, exactness). More specifically, the idea is that
 the structure of a subobject classifier is local: if a category `C` has a subobject classifier,
 then each slice category `C/x` also has a subobject classifier (assuming that `C` has finite
 limits), and the pullback functors `C/y ⟶ C/x` preserve subobject classifiers. In addition,
 this construction is suitably pseudofunctorial.

 Note that we do not instantiate the machinery of local properties to subobject classifier
 types. The reason for that is that the development of local properties is targeted at
 categories without the assumption of finite limits, because several local properties (such as
 extensiveness) do not assume the presence of finite limits. However, to formulate subobject
 classifiers, we need a terminal object, which is a special case of finite limits.

 References
 - "The biequivalence of locally cartesian closed categories and Martin-Löf type theories" by
   Clairambault and Dybjer

 Contents
 1. Lemmas on equivalences and subobject classifiers
 2. The extended pseudofunctor from categories to comprehension categories
 3. The extended pseudofunctor from comprehension categories to categories
 4. The unit
 5. The counit
 6. The displayed biequivalence

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseSubobjectClassifier.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodSubobjectClassifier.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
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
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SubobjectTypes.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Lemmas on equivalences and subobject classifiers *)
Proposition identity_preserves_subobject_classifier'
            {C : univalent_category}
            {T₁ : Terminal C}
            {T₂ : Terminal C}
            (FT : preserves_terminal (functor_identity C))
  : preserves_subobject_classifier (functor_identity C) T₁ T₂ FT.
Proof.
  assert (T₁ = T₂) as p.
  {
    apply isaprop_Terminal.
    apply univalent_category_is_univalent.
  }
  rewrite p.
  clear p.
  assert (FT = identity_preserves_terminal C) as p.
  {
    apply isaprop_preserves_terminal.
  }
  rewrite p.
  exact (identity_preserves_subobject_classifier T₂).
Qed.

Proposition preserves_subobject_classifier_adj_equiv
            {C₁ C₂ : bicat_of_univ_cats}
            (F : adjoint_equivalence C₁ C₂)
            {T₁ : Terminal (C₁ : univalent_category)}
            {T₂ : Terminal (C₂ : univalent_category)}
            (FT : preserves_terminal (pr1 F))
  : preserves_subobject_classifier (pr1 F) T₁ T₂ FT.
Proof.
  revert C₁ C₂ F T₁ T₂ FT.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C T₁ T₂ FT Ω₁ Ω₂.
  apply identity_preserves_subobject_classifier'.
Qed.

Proposition preserves_subobject_classifier_left_adjoint_equivalence
            {C₁ C₂ : univalent_category}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (F : bicat_of_univ_cats ⟦ C₁, C₂ ⟧)
            (HF : left_adjoint_equivalence F)
            (FT : preserves_terminal F)
  : preserves_subobject_classifier F T₁ T₂ FT.
Proof.
  exact (preserves_subobject_classifier_adj_equiv (F ,, HF) FT).
Qed.

Proposition preserves_subobject_classifier_adj_equivalence_of_cats
            {C₁ C₂ : univalent_category}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (F : C₁ ⟶ C₂)
            (FT : preserves_terminal F)
            (HF : adj_equivalence_of_cats F)
  : preserves_subobject_classifier F T₁ T₂ FT.
Proof.
  refine (preserves_subobject_classifier_left_adjoint_equivalence F _ FT).
  use equiv_cat_to_adj_equiv.
  exact HF.
Qed.

Proposition preserves_subobject_classifier_adj_equivalence_of_cats'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (F : C₁ ⟶ C₂)
            (FT : preserves_terminal F)
            (HF : adj_equivalence_of_cats F)
            (Ω₁ : subobject_classifier T₁)
            (Ω₂ : subobject_classifier T₂)
  : preserves_subobject_classifier F T₁ T₂ FT.
Proof.
  exact (preserves_subobject_classifier_adj_equivalence_of_cats
           (C₁ := make_univalent_category C₁ HC₁)
           (C₂ := make_univalent_category C₂ HC₂)
           F
           FT
           HF).
Qed.

Proposition subobject_classifier_adj_equiv_f_help
            {C₁ C₂ : bicat_of_univ_cats}
            (F : adjoint_equivalence C₁ C₂)
            {T₁ : Terminal (C₁ : univalent_category)}
            {T₂ : Terminal (C₂ : univalent_category)}
            (Ω : subobject_classifier T₁)
  : subobject_classifier T₂.
Proof.
  revert C₁ C₂ F T₁ T₂ Ω.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C T₁ T₂ Ω.
  assert (T₁ = T₂) as p.
  {
    apply isaprop_Terminal.
    apply univalent_category_is_univalent.
  }
  rewrite <- p.
  exact Ω.
Qed.

Proposition subobject_classifier_left_adjoint_equivalence_f
            {C₁ C₂ : univalent_category}
            (F : bicat_of_univ_cats ⟦ C₁ , C₂ ⟧)
            (HF : left_adjoint_equivalence F)
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (Ω : subobject_classifier T₁)
  : subobject_classifier T₂.
Proof.
  use (subobject_classifier_adj_equiv_f_help _ Ω).
  exact (F ,, HF).
Qed.

Proposition subobject_classifier_adj_equiv_f
            {C₁ C₂ : univalent_category}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            (Ω : subobject_classifier T₁)
  : subobject_classifier T₂.
Proof.
  use (subobject_classifier_left_adjoint_equivalence_f _ _ Ω).
  - exact F.
  - use equiv_cat_to_adj_equiv.
    exact HF.
Qed.

Proposition subobject_classifier_adj_equiv_f'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            (F : C₁ ⟶ C₂)
            (HF : adj_equivalence_of_cats F)
            (Ω : subobject_classifier T₁)
  : subobject_classifier T₂.
Proof.
  exact (@subobject_classifier_adj_equiv_f
           (make_univalent_category C₁ HC₁)
           (make_univalent_category C₂ HC₂)
           T₁ T₂
           F
           HF
           Ω).
Qed.

Proposition preserves_subobject_classifier_nat_z_iso_f_help
            {C₁ C₂ : bicat_of_univ_cats}
            {TC₁ : Terminal (C₁ : univalent_category)}
            {TC₂ : Terminal (C₂ : univalent_category)}
            {F G : C₁ --> C₂}
            (FT : preserves_terminal F)
            (GT : preserves_terminal G)
            (τ : invertible_2cell F G)
            (HF : preserves_subobject_classifier F TC₁ TC₂ FT)
  : preserves_subobject_classifier G TC₁ TC₂ GT.
Proof.
  revert C₁ C₂ F G τ TC₁ TC₂ FT GT HF.
  use J_2_1.
  {
    exact univalent_cat_is_univalent_2_1.
  }
  intros C₁ C₂ F T₁ T₂ FT GT HF.
  assert (FT = GT) as p.
  {
    apply isaprop_preserves_terminal.
  }
  induction p.
  exact HF.
Qed.

Proposition preserves_subobject_classifier_nat_z_iso_f
            {C₁ C₂ : univalent_category}
            {TC₁ : Terminal (C₁ : univalent_category)}
            {TC₂ : Terminal (C₂ : univalent_category)}
            {F G : C₁ ⟶ C₂}
            (FT : preserves_terminal F)
            (GT : preserves_terminal G)
            (τ : nat_z_iso F G)
            (HF : preserves_subobject_classifier F TC₁ TC₂ FT)
  : preserves_subobject_classifier G TC₁ TC₂ GT.
Proof.
  use (preserves_subobject_classifier_nat_z_iso_f_help FT GT _ HF).
  use nat_z_iso_to_invertible_2cell.
  exact τ.
Qed.

Proposition preserves_subobject_classifier_nat_z_iso_adj_equiv_f_help
            {C₁ C₂ D₁ D₂ : bicat_of_univ_cats}
            {TC₁ : Terminal (C₁ : univalent_category)}
            {TC₂ : Terminal (C₂ : univalent_category)}
            {TD₁ : Terminal (D₁ : univalent_category)}
            {TD₂ : Terminal (D₂ : univalent_category)}
            (EC : adjoint_equivalence C₁ C₂)
            (ED : adjoint_equivalence D₁ D₂)
            {F : C₁ --> D₁}
            (FT : preserves_terminal F)
            {G : C₂ --> D₂}
            (GT : preserves_terminal G)
            (τ : nat_z_iso (F ∙ pr1 ED) (pr1 EC ∙ G))
            (HF : preserves_subobject_classifier F TC₁ TD₁ FT)
  : preserves_subobject_classifier G TC₂ TD₂ GT.
Proof.
  revert C₁ C₂ EC D₁ D₂ ED TC₁ TC₂ TD₁ TD₂ F FT G GT τ HF.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros C.
  use J_2_0.
  {
    exact univalent_cat_is_univalent_2_0.
  }
  intros D HC₁ HC₂ HD₁ HD₂ F FT G GT τ HF.
  assert (HC₁ = HC₂) as p.
  {
    apply isaprop_Terminal.
    apply univalent_category_is_univalent.
  }
  induction p.
  assert (HD₁ = HD₂) as p.
  {
    apply isaprop_Terminal.
    apply univalent_category_is_univalent.
  }
  induction p.
  exact (preserves_subobject_classifier_nat_z_iso_f FT GT τ HF).
Qed.

Proposition preserves_subobject_classifier_nat_z_iso_adj_equiv_f
            {C₁ C₂ D₁ D₂ : univalent_category}
            {TC₁ : Terminal C₁}
            {TC₂ : Terminal C₂}
            {TD₁ : Terminal D₁}
            {TD₂ : Terminal D₂}
            {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
            (HEC : adj_equivalence_of_cats EC)
            (HED : adj_equivalence_of_cats ED)
            {F : C₁ ⟶ D₁}
            (FT : preserves_terminal F)
            {G : C₂ ⟶ D₂}
            (GT : preserves_terminal G)
            (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
            (HF : preserves_subobject_classifier F TC₁ TD₁ FT)
  : preserves_subobject_classifier G TC₂ TD₂ GT.
Proof.
  refine (preserves_subobject_classifier_nat_z_iso_adj_equiv_f_help
            (EC ,, _) (ED ,, _)
            FT GT
            τ HF).
  - use equiv_cat_to_adj_equiv.
    exact HEC.
  - use equiv_cat_to_adj_equiv.
    exact HED.
Qed.

Proposition preserves_subobject_classifier_nat_z_iso_adj_equiv_f'
            {C₁ C₂ D₁ D₂ : category}
            (HC₁' : is_univalent C₁)
            (HC₂' : is_univalent C₂)
            (HD₁' : is_univalent D₁)
            (HD₂' : is_univalent D₂)
            {TC₁ : Terminal C₁}
            {TC₂ : Terminal C₂}
            {TD₁ : Terminal D₁}
            {TD₂ : Terminal D₂}
            {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
            (HEC : adj_equivalence_of_cats EC)
            (HED : adj_equivalence_of_cats ED)
            {F : C₁ ⟶ D₁}
            (FT : preserves_terminal F)
            {G : C₂ ⟶ D₂}
            (GT : preserves_terminal G)
            (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
            (HF : preserves_subobject_classifier F TC₁ TD₁ FT)
  : preserves_subobject_classifier G TC₂ TD₂ GT.
Proof.
  exact (preserves_subobject_classifier_nat_z_iso_adj_equiv_f
           (C₁ := make_univalent_category C₁ HC₁')
           (C₂ := make_univalent_category C₂ HC₂')
           (D₁ := make_univalent_category D₁ HD₁')
           (D₂ := make_univalent_category D₂ HD₂')
           HEC HED
           FT GT
           τ
           HF).
Qed.

(** * 2. The extended pseudofunctor from categories to comprehension categories *)
Definition finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier
  : disp_psfunctor
      disp_bicat_finlim_subobject_classifier
      disp_bicat_of_subobject_classifier_type
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type.
  - apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
  - refine (λ (C : univ_cat_with_finlim) Ω, _ ,, tt).
    exact (codomain_fiberwise_subobject_classifier
             (terminal_univ_cat_with_finlim C)
             (pullbacks_univ_cat_with_finlim C)
             (pr1 Ω)).
  - refine (λ (C₁ C₂ : univ_cat_with_finlim)
              (F : functor_finlim C₁ C₂)
              Ω₁ Ω₂
              HF,
            tt ,, _).
    exact (preserves_subobject_classifier_disp_codomain_fiber_functor
             (binproducts_univ_cat_with_finlim C₁)
             (binproducts_univ_cat_with_finlim C₂)
             (pr1 Ω₁)
             (pr1 Ω₂)
             F
             _
             (functor_finlim_preserves_binproduct F)
             (pr2 HF)).
Defined.

(** * 3. The extended pseudofunctor from comprehension categories to categories *)
Definition subobject_classifier_in_dfl_comp_cat
           (C : dfl_full_comp_cat)
           (Ω : fiberwise_subobject_classifier
                  (fiberwise_terminal_dfl_full_comp_cat C))
  : subobject_classifier (empty_context C).
Proof.
  use (subobject_classifier_adj_equiv_f' _ _ _ (dfl_full_comp_cat_adjequiv_base C)).
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply univalent_category_is_univalent.
  - apply fiberwise_terminal_dfl_full_comp_cat.
  - apply Ω.
Qed.

Definition subobject_classifier_in_dfl_comp_cat_functor
           {C₁ C₂ : dfl_full_comp_cat}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (Ω₁ : fiberwise_subobject_classifier
                   (fiberwise_terminal_dfl_full_comp_cat C₁))
           (Ω₂ : fiberwise_subobject_classifier
                   (fiberwise_terminal_dfl_full_comp_cat C₂))
           (HF : preserves_fiberwise_subobject_classifier
                   (fiberwise_terminal_dfl_full_comp_cat C₁)
                   (fiberwise_terminal_dfl_full_comp_cat C₂)
                   (comp_cat_type_functor F)
                   (preserves_terminal_dfl_full_comp_cat_functor F))
  : preserves_subobject_classifier F [] [] (comp_cat_functor_terminal F).
Proof.
  use (preserves_subobject_classifier_nat_z_iso_adj_equiv_f'
         _ _ _ _ _ _ _ _
         (dfl_functor_nat_z_iso F)
         (HF _ )).
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply univalent_category_is_univalent.
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply univalent_category_is_univalent.
  - use comp_adj_equivalence_of_cats.
    + apply dfl_full_comp_cat_adjequiv_empty.
    + apply cod_fib_terminal.
  - pose (T := make_Terminal _ (comp_cat_functor_terminal F [] (pr2 []))).
    use comp_adj_equivalence_of_cats.
    + exact (dfl_full_comp_cat_adjequiv_terminal C₂ T).
    + exact (cod_fib_terminal T).
Qed.

Definition dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier
  : disp_psfunctor
      disp_bicat_of_subobject_classifier_type
      disp_bicat_finlim_subobject_classifier
      dfl_comp_cat_to_finlim_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - apply disp_2cells_iscontr_finlim_subobject_classifier.
  - apply disp_locally_groupoid_finlim_subobject_classifier.
  - exact (λ (C : dfl_full_comp_cat) Ω,
           subobject_classifier_in_dfl_comp_cat C (pr1 Ω)
           ,,
           tt).
  - refine (λ (C₁ C₂ : dfl_full_comp_cat)
              (F : dfl_full_comp_cat_functor C₁ C₂)
              Ω₁ Ω₂
              HF,
             tt ,, _).
    exact (subobject_classifier_in_dfl_comp_cat_functor (pr1 Ω₁) (pr1 Ω₂) (pr2 HF)).
Defined.

(** * 4. The unit *)
Definition finlim_dfl_comp_cat_unit_subobject_classifier
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier
         dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_unit.
Proof.
  use make_disp_pstrans_contr.
  - apply disp_2cells_iscontr_finlim_subobject_classifier.
  - apply disp_locally_groupoid_finlim_subobject_classifier.
  - intros C H.
    refine (tt ,, _) ; cbn.
    apply identity_preserves_subobject_classifier.
Qed.

Definition finlim_dfl_comp_cat_unit_subobject_classifier_pointwise_adjequiv
           {C : univ_cat_with_finlim}
           (HC : disp_bicat_finlim_subobject_classifier C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_unit_pointwise_equiv C)
      (finlim_dfl_comp_cat_unit_subobject_classifier C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_of_univ_cat_subobject_classifier.
Qed.

Definition finlim_dfl_comp_cat_unit_inv_subobject_classifier
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier
         dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier)
      finlim_dfl_comp_cat_unit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - apply disp_2cells_iscontr_finlim_subobject_classifier.
  - apply disp_locally_groupoid_finlim_subobject_classifier.
  - apply finlim_dfl_comp_cat_unit_subobject_classifier.
  - intros.
    apply finlim_dfl_comp_cat_unit_subobject_classifier_pointwise_adjequiv.
Qed.

(** * 5. The counit *)
Definition finlim_dfl_comp_cat_counit_subobject_classifier
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier)
      finlim_dfl_comp_cat_counit.
Proof.
  use make_disp_pstrans_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type.
  - apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
  - refine (λ C Ω, tt ,, _).
    induction Ω as [ Ω [ ] ].
    intro x ; cbn ; cbn in x, Ω.
    use (preserves_subobject_classifier_adj_equivalence_of_cats'
           _ _ _ _
           (fiber_functor_comprehension_adj_equiv C x)).
    + apply is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    + apply is_univalent_fiber.
      apply disp_univalent_disp_codomain.
    + apply Ω.
    + use cod_fib_subobject_classifier.
      * apply empty_context.
      * apply binproducts_dfl_full_comp_cat.
      * apply subobject_classifier_in_dfl_comp_cat.
        exact Ω.
Qed.

Definition finlim_dfl_comp_cat_counit_subobject_classifier_pointwise_adjequiv
           {C : dfl_full_comp_cat}
           (HC : disp_bicat_of_subobject_classifier_type C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_counit_pointwise_equiv C)
      (finlim_dfl_comp_cat_counit_subobject_classifier C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_of_subobject_classifier_type.
Qed.

Definition finlim_dfl_comp_cat_counit_inv_subobject_classifier
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_counit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type.
  - apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
  - apply finlim_dfl_comp_cat_counit_subobject_classifier.
  - intros.
    apply finlim_dfl_comp_cat_counit_subobject_classifier_pointwise_adjequiv.
Qed.

(** * 6. The displayed biequivalence *)
Definition finlim_dfl_comp_cat_biequivalence_unit_counit_subobject_classifier
  : is_disp_biequivalence_unit_counit
      _ _
      finlim_dfl_comp_cat_biequivalence_unit_counit
      finlim_biequiv_dfl_comp_cat_disp_psfunctor_subobject_classifier
      dfl_comp_cat_to_finlim_disp_psfunctor_subobject_classifier.
Proof.
  simple refine (_ ,, _).
  - exact finlim_dfl_comp_cat_unit_subobject_classifier.
  - exact finlim_dfl_comp_cat_counit_inv_subobject_classifier.
Defined.

Definition finlim_biequiv_dfl_comp_cat_psfunctor_subobject_classifier
  : disp_is_biequivalence_data
      _
      _
      finlim_dfl_comp_cat_biequivalence_adjoints
      finlim_dfl_comp_cat_biequivalence_unit_counit_subobject_classifier.
Proof.
  simple refine (_ ,, _ ,, (_ ,, _) ,, (_ ,, _)).
  - exact finlim_dfl_comp_cat_unit_inv_subobject_classifier.
  - exact finlim_dfl_comp_cat_counit_subobject_classifier.
  - use make_disp_invmodification_contr.
    + apply disp_2cells_iscontr_finlim_subobject_classifier.
    + apply disp_locally_groupoid_finlim_subobject_classifier.
  - use make_disp_invmodification_contr.
    + apply disp_2cells_iscontr_finlim_subobject_classifier.
    + apply disp_locally_groupoid_finlim_subobject_classifier.
  - use make_disp_invmodification_contr.
    + apply disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type.
    + apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
  - use make_disp_invmodification_contr.
    + apply disp_2cells_iscontr_disp_bicat_of_subobject_classifier_type.
    + apply disp_locally_groupoid_disp_bicat_of_subobject_classifier_type.
Defined.
