(*******************************************************************************************

 The pseudofunctor from DFL comprehension categories to categories with finite limits

 In this file, we construct a pseudofunctor from the bicategory of DFL comprehension categories
 to the bicategory of categories with finite limits. This functor sends every DFL comprehension
 category to its category of contexts. As such, we have to show that the category of contexts
 has all finite limits. The reason why this is so, is because the category of context is
 equivalent to the category of types in the empty context due to democracy. In addition,
 since we assume there to be equalizer types and product types, we get that the category
 of contexts has equalizers and products. Since the category of context also has a terminal
 object (i.e., the empty context), we get all finite limits.

 This pseudofunctor sends every functor between DFL comprehension categories to its underlying
 functor on the categories on context. Using similar reasoning, we conclude that this functor
 must preserve all finite limits.

 Contents
 1. The action on objects
 2. The action on morphisms
 3. The action on 2-cells
 4. The identitor and compositor
 5. The data of the pseudofunctor
 6. The laws of the pseudofunctor
 7. The pseudofunctor from DFL comprehension categories to categories with finite limits

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
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
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.EquivalencePreservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.whiskering.
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
Local Open Scope comp_cat.

(** * 1. The action on objects *)
Section DFLFullCompCatLimits.
  Context (C : dfl_full_comp_cat).

  Definition binproducts_dfl_full_comp_cat
    : BinProducts C.
  Proof.
    use (adj_equiv_preserves_binproducts_f
           (dfl_full_comp_cat_adjequiv_base C)).
    apply fiberwise_binproducts_dfl_full_comp_cat.
  Defined.

  Definition equalizers_dfl_full_comp_cat
    : Equalizers C.
  Proof.
    use (adj_equiv_preserves_equalizers_f
           (dfl_full_comp_cat_adjequiv_base C)).
    apply fiberwise_equalizers_dfl_full_comp_cat.
  Defined.
End DFLFullCompCatLimits.

Definition dfl_full_comp_cat_to_finlim
           (C : dfl_full_comp_cat)
  : univ_cat_with_finlim.
Proof.
  use make_univ_cat_with_finlim.
  - exact C.
  - exact [].
  - use Pullbacks_from_Equalizers_BinProducts.
    + exact (binproducts_dfl_full_comp_cat C).
    + exact (equalizers_dfl_full_comp_cat C).
Defined.

(** * 2. The action on morphisms *)
Section DFLFullCompCatLimitPreservation.
  Context {C₁ C₂ : dfl_full_comp_cat}
          (F : dfl_full_comp_cat_functor C₁ C₂).

  (**
   To construct the action on morphisms, one needs to show that the underlying
   functor of a functor between comprehension categories preserves both equalizers
   and binary products. The idea is that we have a diagram of functors commutes up
   to natural isomorphism. This diagram consists of two squares: one is given by `τ`
   and the other is given by `θ` below. The horizontal sides, which are `χ₁ ∙ E₁` and
   `χ₂ ∙ E₂`, of this square are adjoint equivalences, and for that reason, the functor
   `F` preserves products and equalizers whenever the fiber functor does. Since we
   assume product types and equalizer types to be stable under substitution, the fiber
   functor indeed preserves them, and thus `F` does so as well.
   *)
  Let T₂ : Terminal C₂
    := make_Terminal _ (comp_cat_functor_terminal F [] (pr2 [])).

  Let χ₁ : (disp_cat_of_types C₁)[{[]}] ⟶ (disp_codomain C₁)[{[]}]
    := fiber_functor (comp_cat_comprehension C₁) [].
  Let χ₂ : (disp_cat_of_types C₂)[{F []}] ⟶ (disp_codomain C₂)[{F []}]
    := fiber_functor (comp_cat_comprehension C₂) (F []).
  Let FF : (disp_cat_of_types C₁)[{[]}] ⟶ (disp_cat_of_types C₂)[{F []}]
    := fiber_functor (comp_cat_type_functor F) [].
  Let Farr : (disp_codomain C₁)[{[]}] ⟶ (disp_codomain C₂)[{F []}]
    := fiber_functor (disp_codomain_functor F) [].
  Let τ : nat_z_iso (FF ∙ χ₂) (χ₁ ∙ Farr)
    := full_comp_cat_fiber_nat_z_iso_inv F [].

  Let E₁ : (C₁ / []) ⟶ C₁
    := cod_fib_terminal_to_base [].
  Let E₂ : (C₂ / T₂) ⟶ C₂
    := cod_fib_terminal_to_base T₂.

  Let θ : nat_z_iso (Farr ∙ E₂) (E₁ ∙ F)
    := cod_fib_terminal_to_base_nat_z_iso
         F
         (comp_cat_functor_terminal F)
         [].

  Definition dfl_functor_nat_z_iso
    : nat_z_iso (FF ∙ (χ₂ ∙ E₂)) ((χ₁ ∙ E₁) ∙ F)
    := nat_z_iso_comp
         (post_whisker_nat_z_iso τ E₂)
         (pre_whisker_nat_z_iso χ₁ θ).

  Let τθ : nat_z_iso (FF ∙ (χ₂ ∙ E₂)) ((χ₁ ∙ E₁) ∙ F)
    := dfl_functor_nat_z_iso.

  Definition preserves_binproduct_binproducts_dfl_functor
    : preserves_binproduct F.
  Proof.
    use (preserves_binproduct_equivalence_f _ _ _ _ _ _ τθ).
    - use comp_adj_equivalence_of_cats.
      + apply dfl_full_comp_cat_adjequiv_empty.
      + apply cod_fib_terminal.
    - use comp_adj_equivalence_of_cats.
      + exact (dfl_full_comp_cat_adjequiv_terminal C₂ T₂).
      + exact (cod_fib_terminal T₂).
    - apply preserves_binproducts_dfl_full_comp_cat_functor.
  Defined.

  Definition preserves_equalizer_binproducts_dfl_functor
    : preserves_equalizer F.
  Proof.
     use (preserves_equalizer_equivalence_f _ _ _ _ _ _ τθ).
    - use comp_adj_equivalence_of_cats.
      + apply dfl_full_comp_cat_adjequiv_empty.
      + apply cod_fib_terminal.
    - use comp_adj_equivalence_of_cats.
      + exact (dfl_full_comp_cat_adjequiv_terminal C₂ T₂).
      + exact (cod_fib_terminal T₂).
    - apply preserves_equalizers_dfl_full_comp_cat_functor.
  Defined.
End DFLFullCompCatLimitPreservation.

Definition dfl_functor_comp_cat_to_finlim_functor
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
  : functor_finlim
      (dfl_full_comp_cat_to_finlim C₁)
      (dfl_full_comp_cat_to_finlim C₂).
Proof.
  use make_functor_finlim.
  - exact F.
  - exact (comp_cat_functor_terminal F).
  - use preserves_pullback_from_binproduct_equalizer.
    + exact (binproducts_dfl_full_comp_cat C₁).
    + exact (equalizers_dfl_full_comp_cat C₁).
    + exact (preserves_binproduct_binproducts_dfl_functor F).
    + exact (preserves_equalizer_binproducts_dfl_functor F).
Defined.

(** * 3. The action on 2-cells *)
Definition dfl_functor_comp_cat_to_finlim_nat_trans
           {C₁ C₂ : dfl_full_comp_cat}
           {F G : dfl_full_comp_cat_functor C₁ C₂}
           (τ : dfl_full_comp_cat_nat_trans F G)
  : nat_trans_finlim
      (dfl_functor_comp_cat_to_finlim_functor F)
      (dfl_functor_comp_cat_to_finlim_functor G).
Proof.
  use make_nat_trans_finlim.
  exact τ.
Defined.

(** * 4. The identitor and compositor *)
Definition dfl_functor_comp_cat_to_finlim_identitor
           (C : dfl_full_comp_cat)
  : id₁ (dfl_full_comp_cat_to_finlim C)
    ==>
    dfl_functor_comp_cat_to_finlim_functor (id₁ C).
Proof.
  use make_nat_trans_finlim.
  apply nat_trans_id.
Defined.

Definition dfl_functor_comp_cat_to_finlim_compositor
           {C₁ C₂ C₃ : bicat_of_dfl_full_comp_cat}
           (F : C₁ --> C₂)
           (G : C₂ --> C₃)
  : dfl_functor_comp_cat_to_finlim_functor F · dfl_functor_comp_cat_to_finlim_functor G
    ==>
    dfl_functor_comp_cat_to_finlim_functor (F · G).
Proof.
  use make_nat_trans_finlim.
  apply nat_trans_id.
Defined.

(** * 5. The data of the pseudofunctor *)
Definition dfl_full_comp_cat_to_finlim_psfunctor_data
  : psfunctor_data
      bicat_of_dfl_full_comp_cat
      bicat_of_univ_cat_with_finlim.
Proof.
  use make_psfunctor_data.
  - exact dfl_full_comp_cat_to_finlim.
  - exact (λ _ _ F, dfl_functor_comp_cat_to_finlim_functor F).
  - exact (λ _ _ _ _ τ, dfl_functor_comp_cat_to_finlim_nat_trans τ).
  - exact dfl_functor_comp_cat_to_finlim_identitor.
  - exact (λ _ _ _ F G, dfl_functor_comp_cat_to_finlim_compositor F G).
Defined.

(** * 6. The laws of the pseudofunctor *)
Proposition dfl_full_comp_cat_to_finlim_psfunctor_laws
  : psfunctor_laws dfl_full_comp_cat_to_finlim_psfunctor_data.
Proof.
  refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _) ;
    intro ; intros ;
    use nat_trans_finlim_eq ;
    intro ; cbn.
  - apply idpath.
  - apply idpath.
  - rewrite !id_right.
    exact (!(functor_id _ _)).
  - rewrite !id_right.
    apply idpath.
  - rewrite !id_left, !id_right.
    exact (!(functor_id _ _)).
  - rewrite !id_left, !id_right.
    apply idpath.
  - rewrite !id_left, !id_right.
    apply idpath.
Qed.

Definition dfl_full_comp_cat_to_finlim_invertible_cells
  : invertible_cells dfl_full_comp_cat_to_finlim_psfunctor_data.
Proof.
  split.
  - intro C.
    use is_invertible_2cell_cat_with_finlim.
    apply is_nat_z_iso_nat_trans_id.
  - intros C₁ C₂ C₃ F G.
    use is_invertible_2cell_cat_with_finlim.
    apply is_nat_z_iso_nat_trans_id.
Defined.

(** * 7. The pseudofunctor from DFL comprehension categories to categories with finite limits *)
Definition dfl_comp_cat_to_finlim_psfunctor
  : psfunctor
      bicat_of_dfl_full_comp_cat
      bicat_of_univ_cat_with_finlim.
Proof.
  use make_psfunctor.
  - exact dfl_full_comp_cat_to_finlim_psfunctor_data.
  - exact dfl_full_comp_cat_to_finlim_psfunctor_laws.
  - exact dfl_full_comp_cat_to_finlim_invertible_cells.
Defined.
