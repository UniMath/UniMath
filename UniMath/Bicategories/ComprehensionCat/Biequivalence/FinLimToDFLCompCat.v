(*******************************************************************************************

 The pseudofunctor from finite limit categories to DFL comprehension categories

 Every category with finite limits gives rise to a full DFL comprehension category. Here the
 fibration is given by the codomain fibration and the comprehension functor is given by the
 identity. Since the category has finite limits, the resulting comprehension category has a
 unit type, product types, and sigma types. It is also democratic by construction. Intuitively,
 this pseudofunctor sends a category with finite limits to its internal language.

 This construction is pseudofunctorial, which is what we show in this file. The main challenge
 of the construction lies in the fact that we are working with rather large and complicated
 objects.

 Contents
 1. The action on objects
 2. The action on morphisms
 3. The action on 2-cells
 4. The identitor and compositor
 5. The data
 6. The laws
 7. The pseudofunctor from categories with finite limits to DFL comprehension categories

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.FullyFaithfulDispFunctor.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.EquivalencePreservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.

(** * 1. The action on objects *)
Section FinLimToDFLCompCat.
  Context (C : univ_cat_with_finlim).

  Definition finlim_to_cat_with_terminal_disp_cat
    : cat_with_terminal_disp_cat.
  Proof.
    use make_cat_with_terminal_disp_cat.
    - exact C.
    - exact (terminal_univ_cat_with_finlim C).
    - exact (univalent_disp_codomain C).
  Defined.

  Definition finlim_to_cat_with_terminal_cleaving
    : cat_with_terminal_cleaving.
  Proof.
    use make_cat_with_terminal_cleaving.
    - exact finlim_to_cat_with_terminal_disp_cat.
    - exact (disp_codomain_cleaving (pullbacks_univ_cat_with_finlim C)).
  Defined.

  Definition finlim_comprehension
    : comprehension_functor finlim_to_cat_with_terminal_cleaving
    := id_cartesian_disp_functor _.

  Definition finlim_to_comp_cat
    : comp_cat.
  Proof.
    use make_comp_cat.
    - exact finlim_to_cat_with_terminal_cleaving.
    - exact finlim_comprehension.
  Defined.

  Definition finlim_to_full_comp_cat
    : full_comp_cat.
  Proof.
    use make_full_comp_cat.
    - exact finlim_to_comp_cat.
    - apply disp_functor_ff_disp_functor_id.
  Defined.

  Definition is_democratic_finlim
    : is_democratic finlim_to_full_comp_cat.
  Proof.
    simple refine (λ (x : C), _ ,, _).
    - refine (x ,, _).
      apply TerminalArrow.
    - apply identity_z_iso.
  Defined.

  Definition finlim_to_dfl_comp_cat_strong_sums
    : strong_dependent_sums finlim_to_full_comp_cat.
  Proof.
    refine (cod_fiber_has_dependent_sum _ ,, _).
    intros Γ A B.
    use is_z_isomorphism_path.
    - apply identity.
    - abstract
        (unfold dependent_sum_map ; cbn ;
         refine (!_) ;
         apply PullbackArrow_PullbackPr1).
    - apply is_z_isomorphism_identity.
  Defined.

  Definition finlim_to_dfl_comp_cat
    : dfl_full_comp_cat.
  Proof.
    use make_dfl_full_comp_cat.
    - exact finlim_to_full_comp_cat.
    - exact is_democratic_finlim.
    - apply codomain_fiberwise_terminal.
    - intro Γ ; cbn.
      apply is_z_isomorphism_identity.
    - apply codomain_fiberwise_binproducts.
    - apply codomain_fiberwise_equalizers.
      exact (terminal_univ_cat_with_finlim C).
    - exact finlim_to_dfl_comp_cat_strong_sums.
  Defined.
End FinLimToDFLCompCat.

(** * 2. The action on morphisms *)
Section FinLimToDFLCompCatFunctor.
  Context {C₁ C₂ : univ_cat_with_finlim}
          (F : functor_finlim C₁ C₂).

  Definition finlim_to_functor_with_terminal_disp_cat
    : functor_with_terminal_disp_cat
        (finlim_to_dfl_comp_cat C₁)
        (finlim_to_dfl_comp_cat C₂).
  Proof.
    use make_functor_with_terminal_disp_cat.
    - exact F.
    - exact (functor_finlim_preserves_terminal F).
    - exact (disp_codomain_functor F).
  Defined.

  Definition finlim_to_functor_with_terminal_cleaving
    : functor_with_terminal_cleaving
        (finlim_to_dfl_comp_cat C₁)
        (finlim_to_dfl_comp_cat C₂).
  Proof.
    use make_functor_with_terminal_cleaving.
    - exact finlim_to_functor_with_terminal_disp_cat.
    - apply is_cartesian_disp_codomain_functor.
      exact (functor_finlim_preserves_pullback F).
  Defined.

  Definition finlim_to_comp_cat_functor_disp_nat_trans
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite
           (disp_functor_identity _)
           (disp_codomain_functor F))
        (disp_functor_composite
           (disp_codomain_functor F)
           (disp_functor_identity _)).
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, id_disp _).
    - abstract
        (intros x y f xx yy ff ;
         use eq_cod_mor ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ; cbn ;
         rewrite id_right, id_left ;
         apply idpath).
  Defined.

  Definition finlim_to_comp_cat_functor
    : comp_cat_functor
        (finlim_to_dfl_comp_cat C₁)
        (finlim_to_dfl_comp_cat C₂).
  Proof.
    use make_comp_cat_functor.
    - exact finlim_to_functor_with_terminal_cleaving.
    - exact finlim_to_comp_cat_functor_disp_nat_trans.
  Defined.

  Definition finlim_to_full_comp_cat_functor
    : full_comp_cat_functor
        (finlim_to_dfl_comp_cat C₁)
        (finlim_to_dfl_comp_cat C₂).
  Proof.
    use make_full_comp_cat_functor.
    - exact finlim_to_comp_cat_functor.
    - intros x xx.
      apply is_z_isomorphism_identity.
  Defined.

  Definition finlim_to_dfl_comp_cat_functor
    : dfl_full_comp_cat_functor
        (finlim_to_dfl_comp_cat C₁)
        (finlim_to_dfl_comp_cat C₂).
  Proof.
    use make_dfl_full_comp_cat_functor.
    - exact finlim_to_full_comp_cat_functor.
    - intro x ; cbn.
      apply preserves_terminal_fiber_disp_codomain_functor.
    - intro x ; cbn.
      apply preserves_binproduct_fiber_disp_codomain_functor.
      exact (functor_finlim_preserves_pullback F).
    - intro x ; cbn.
      apply preserves_equalizer_fiber_disp_codomain_functor.
      use preserves_equalizer_from_pullback_terminal.
      + exact (terminal_univ_cat_with_finlim C₁).
      + exact (pullbacks_univ_cat_with_finlim C₁).
      + exact (functor_finlim_preserves_pullback F).
      + exact (functor_finlim_preserves_terminal F).
  Defined.
End FinLimToDFLCompCatFunctor.

(** * 3. The action on 2-cells *)
Section FinLimToDFLCompCatNatTrans.
  Context {C₁ C₂ : univ_cat_with_finlim}
          {F G : functor_finlim C₁ C₂}
          (τ : nat_trans_finlim F G).

  Definition finlim_to_nat_trans_with_terminal_cleaving
    : nat_trans_with_terminal_cleaving
        (finlim_to_dfl_comp_cat_functor F)
        (finlim_to_dfl_comp_cat_functor G).
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - exact τ.
    - exact (disp_codomain_nat_trans τ).
  Defined.

  Definition finlim_to_dfl_comp_cat_nat_trans
    : dfl_full_comp_cat_nat_trans
        (finlim_to_dfl_comp_cat_functor F)
        (finlim_to_dfl_comp_cat_functor G).
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact finlim_to_nat_trans_with_terminal_cleaving.
    - abstract
        (intros x xx ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.
End FinLimToDFLCompCatNatTrans.

(** * 4. The identitor and compositor *)
Section FinLimToDFLCompCatIdentitor.
  Context (C : univ_cat_with_finlim).

  Definition finlim_to_with_terminal_cleaving_identitor_disp_nat_trans
    : disp_nat_trans
        (nat_trans_id _)
        (comp_cat_type_functor (id₁ _))
        (comp_cat_type_functor (finlim_to_dfl_comp_cat_functor (id₁ C))).
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, id_disp _).
    - abstract
        (intros x y f xx yy ff ;
         use eq_cod_mor ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ; cbn ;
         rewrite id_right, id_left ;
         apply idpath).
  Defined.

  Definition finlim_to_with_terminal_cleaving_identitor
    : nat_trans_with_terminal_cleaving
        (id₁ _)
        (finlim_to_dfl_comp_cat_functor (id₁ C)).
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - apply nat_trans_id.
    - exact finlim_to_with_terminal_cleaving_identitor_disp_nat_trans.
  Defined.

  Proposition finlim_to_dfl_comp_cat_identitor_eq
    : comprehension_nat_trans_eq
        finlim_to_with_terminal_cleaving_identitor
        (comp_cat_functor_comprehension (id₁ _))
        (comp_cat_functor_comprehension (finlim_to_dfl_comp_cat_functor (id₁ C))).
  Proof.
    intros x xx ; cbn.
    apply idpath.
  Qed.

  Definition finlim_to_dfl_comp_cat_identitor
    : id₁ (finlim_to_dfl_comp_cat C)
      ==>
      finlim_to_dfl_comp_cat_functor (id₁ C).
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact finlim_to_with_terminal_cleaving_identitor.
    - exact finlim_to_dfl_comp_cat_identitor_eq.
  Defined.
End FinLimToDFLCompCatIdentitor.

Section FinLimToDFLCompCatCompositor.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim}
          (F : functor_finlim C₁ C₂)
          (G : functor_finlim C₂ C₃).

  Let FG : dfl_full_comp_cat_functor
             (finlim_to_dfl_comp_cat C₁)
             (finlim_to_dfl_comp_cat C₃)
    := finlim_to_dfl_comp_cat_functor F · finlim_to_dfl_comp_cat_functor G.

  Definition finlim_to_with_terminal_cleaving_compositor_disp_nat_trans
    : disp_nat_trans
        (nat_trans_id (finlim_to_dfl_comp_cat_functor (F · G)))
        (comp_cat_type_functor FG)
        (comp_cat_type_functor (finlim_to_dfl_comp_cat_functor (F · G))).
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, id_disp _).
    - abstract
        (intros x y f xx yy ff ;
         use eq_cod_mor ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ; cbn ;
         rewrite id_right, id_left ;
         apply idpath).
  Defined.

  Definition finlim_to_with_terminal_cleaving_compositor
    : nat_trans_with_terminal_cleaving
        FG
        (finlim_to_dfl_comp_cat_functor (F · G)).
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - apply nat_trans_id.
    - exact finlim_to_with_terminal_cleaving_compositor_disp_nat_trans.
  Defined.

  Proposition finlim_to_dfl_comp_cat_compositor_eq
    : comprehension_nat_trans_eq
        finlim_to_with_terminal_cleaving_compositor
        (comp_cat_functor_comprehension FG)
        (comp_cat_functor_comprehension (finlim_to_dfl_comp_cat_functor (F · G))).
  Proof.
    intros x xx ; cbn.
    rewrite !id_right.
    apply functor_id.
  Qed.

  Definition finlim_to_dfl_comp_cat_compositor
    : FG
      ==>
      finlim_to_dfl_comp_cat_functor (F · G).
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact finlim_to_with_terminal_cleaving_compositor.
    - exact finlim_to_dfl_comp_cat_compositor_eq.
  Defined.
End FinLimToDFLCompCatCompositor.

(** * 5. The data *)
Definition finlim_to_dfl_comp_cat_psfunctor_data
  : psfunctor_data
      bicat_of_univ_cat_with_finlim
      bicat_of_dfl_full_comp_cat.
Proof.
  use make_psfunctor_data.
  - exact finlim_to_dfl_comp_cat.
  - exact (λ _ _ F, finlim_to_dfl_comp_cat_functor F).
  - exact (λ _ _ _ _ τ, finlim_to_dfl_comp_cat_nat_trans τ).
  - exact finlim_to_dfl_comp_cat_identitor.
  - exact (λ _ _ _ F G, finlim_to_dfl_comp_cat_compositor F G).
Defined.

(** * 6. The laws *)
Proposition finlim_to_dfl_comp_cat_psfunctor_laws
  : psfunctor_laws finlim_to_dfl_comp_cat_psfunctor_data.
Proof.
  refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _) ; intro ; intros.
  - use dfl_full_comp_cat_nat_trans_eq.
    + intro x ; cbn.
      apply idpath.
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      apply idpath.
  - use dfl_full_comp_cat_nat_trans_eq.
    + intro x ; cbn.
      apply idpath.
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      apply idpath.
  - use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ; cbn ;
         rewrite !id_right ;
         exact (!(functor_id _ _))).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_right.
      exact (!(functor_id _ _)).
  - use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ; cbn ;
         rewrite !id_right ;
         apply idpath).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_right.
      apply idpath.
  - use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ; cbn ;
         rewrite !id_left, !id_right ;
         exact (!(functor_id _ _))).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_left, !id_right.
      exact (!(functor_id _ _)).
  - use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ; cbn ;
         rewrite !id_left, !id_right ;
         apply idpath).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_left, !id_right.
      apply idpath.
  - use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ; cbn ;
         rewrite !id_left, !id_right ;
         apply idpath).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_left, !id_right.
      apply idpath.
Qed.

Definition finlim_to_dfl_comp_cat_invertible_cells
  : invertible_cells
      finlim_to_dfl_comp_cat_psfunctor_data.
Proof.
  split.
  - intro C.
    use is_invertible_dfl_full_comp_cat_nat_trans ; cbn.
    + intro x.
      apply is_z_isomorphism_identity.
    + intros x xx.
      use is_z_iso_disp_codomain'.
      apply is_z_isomorphism_identity.
  - intros C₁ C₂ C₃ F G.
    use is_invertible_dfl_full_comp_cat_nat_trans ; cbn.
    + intro x.
      apply is_z_isomorphism_identity.
    + intros x xx.
      use is_z_iso_disp_codomain'.
      apply is_z_isomorphism_identity.
Defined.

(** * 7. The pseudofunctor from categories with finite limits to DFL comprehension categories *)
Definition finlim_to_dfl_comp_cat_psfunctor
  : psfunctor
      bicat_of_univ_cat_with_finlim
      bicat_of_dfl_full_comp_cat.
Proof.
  use make_psfunctor.
  - exact finlim_to_dfl_comp_cat_psfunctor_data.
  - exact finlim_to_dfl_comp_cat_psfunctor_laws.
  - exact finlim_to_dfl_comp_cat_invertible_cells.
Defined.
