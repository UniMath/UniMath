(*******************************************************************************************

 The bicategory of full comprehension categories

 Our goal is to construct the bicategory of full comprehension categories, and to do so, we
 use displayed bicategories. Starting with the bicategory of univalent categories, we add the
 following structure to it in the following order.
 1. A displayed category and a terminal object.
 2. A cleaving for the displayed category.
 3. A comprehension functor.
 4. A proof that this comprehension functor is fully faithful.
 In this file, we look at the last of these.

 Before we explain the construction, we discuss what the 1-cells of this bicategory should be.
 While we used lax morphisms in the bicategory of comprehension categories, we use pseudo
 morphisms for this one. If we have two comprehension categories `C₁` and `C₂` whose
 comprehension functors are given by `χ₁ : D₁ ⟶ Arr(C₁)` and `χ₂ : D₂ ⟶ Arr(C₂)`, then
 a morphisms between them will have functors `FF : D₁ ⟶ D₂` and `Arr(F) : Arr(C₁) ⟶ Arr(C₂)`
 (where `F` is the functor between the base categories of `C₁` and `C₂`). This gives us two
 functors  `D₁ ⟶ Arr(C₂)`, namely `χ₁ · Arr(F)` and `FF · χ₂`. For a pseudo morphism, we
 require a natural isomorphism between these two functors.

 As such, our construction of the bicategory of full comprehension category restricts the
 objects to the full ones (i.e., the comprehension functor is fully faithful), and it restricts
 the morphisms to the pseudo ones (i.e., the natural isomorphisms). For this reason, we define
 the bicategory of full comprehension categories as a subbicategory of the bicategory of
 comprehension categories (and not as a full subbicategory). The univalence of the constructed
 bicategory follows almost directly from the construction.

 References:
 - 'Categorical structures for deduction' by Coraglia (https://etagreta.github.io/docs/coraglia_phdthesis-oneside2023.pdf)
 - 'Categorical Logic and Type Theory' by Jacobs

 Contents
 1. The bicategory of full comprehension categories
 2. The univalence of the bicategory of full comprehension categories
 3. Builders and accessors
 4. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.DispCatTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FibTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.CompCat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.

Local Open Scope cat.

(** * 1. The bicategory of full comprehension categories *)
Definition is_full_comp_cat
           (C : comp_cat)
  : UU
  := disp_functor_ff (comp_cat_comprehension C).

Proposition isaprop_is_full_comp_cat
            (C : comp_cat)
  : isaprop (is_full_comp_cat C).
Proof.
  apply isaprop_disp_functor_ff.
Qed.

Definition disp_bicat_full_comp_cat
  : disp_bicat bicat_comp_cat.
Proof.
  use disp_subbicat.
  - exact is_full_comp_cat.
  - exact (λ (C₁ C₂ : comp_cat)
             (P₁ : is_full_comp_cat C₁)
             (P₂ : is_full_comp_cat C₂)
             (F : comp_cat_functor C₁ C₂),
            ∏ (x : C₁)
              (xx : disp_cat_of_types C₁ x),
            is_z_isomorphism
              (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx)).
  - intros C P x xx.
    apply identity_is_z_iso.
  - intros C₁ C₂ C₃ P₁ P₂ P₃ F G H₁ H₂ x xx.
    cbn.
    use is_z_iso_comp_of_is_z_isos.
    + apply (functor_on_z_iso _ (_ ,, H₁ x xx)).
    + apply H₂.
Defined.

Definition bicat_full_comp_cat
  : bicat
  := total_bicat disp_bicat_full_comp_cat.

(** * 2. The univalence of the bicategory of full comprehension categories *)
Proposition disp_univalent_2_1_disp_bicat_full_comp_cat
  : disp_univalent_2_1 disp_bicat_full_comp_cat.
Proof.
  apply disp_subbicat_univalent_2_1.
  intro ; intros.
  do 2 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

Proposition disp_univalent_2_0_disp_bicat_full_comp_cat
  : disp_univalent_2_0 disp_bicat_full_comp_cat.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_comp_cat.
  - intro.
    apply isaprop_is_full_comp_cat.
  - intros.
    do 2 (use impred ; intro).
    apply isaprop_is_z_isomorphism.
Qed.

Proposition is_univalent_2_1_bicat_full_comp_cat
  : is_univalent_2_1 bicat_full_comp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Proposition is_univalent_2_0_bicat_full_comp_cat
  : is_univalent_2_0 bicat_full_comp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_comp_cat.
  - exact disp_univalent_2_0_disp_bicat_full_comp_cat.
Qed.

Proposition is_univalent_2_bicat_full_comp_cat
  : is_univalent_2 bicat_full_comp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - exact is_univalent_2_1_bicat_full_comp_cat.
Qed.

(** * 3. Builders and accessors *)
Definition full_comp_cat
  : UU
  := bicat_full_comp_cat.

Definition make_full_comp_cat
           (C : comp_cat)
           (H : disp_functor_ff (comp_cat_comprehension C))
  : full_comp_cat
  := C ,, H ,, tt.

Coercion full_comp_cat_to_comp_cat
         (C : full_comp_cat)
  : comp_cat
  := pr1 C.

Definition full_comp_cat_comprehension_fully_faithful
           (C : full_comp_cat)
  : disp_functor_ff (comp_cat_comprehension C)
  := pr12 C.

Definition full_comp_cat_comprehension_fiber_fully_faithful
           {C : full_comp_cat}
           (x : C)
  : fully_faithful (fiber_functor (comp_cat_comprehension C) x).
Proof.
  use fiber_functor_ff.
  exact (full_comp_cat_comprehension_fully_faithful C).
Qed.

Definition full_comp_cat_functor
           (C₁ C₂ : full_comp_cat)
  : UU
  := C₁ --> C₂.

Definition make_full_comp_cat_functor
           {C₁ C₂ : full_comp_cat}
           (F : comp_cat_functor C₁ C₂)
           (HF : ∏ (x : C₁)
                   (xx : disp_cat_of_types C₁ x),
                 is_z_isomorphism
                   (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx))
  : full_comp_cat_functor C₁ C₂
  := F ,, tt ,, HF.

Coercion full_comp_cat_functor_to_comp_cat_functor
         {C₁ C₂ : full_comp_cat}
         (F : full_comp_cat_functor C₁ C₂)
  : comp_cat_functor C₁ C₂
  := pr1 F.

Definition full_comp_cat_functor_is_z_iso
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           {x : C₁}
           (xx : disp_cat_of_types C₁ x)
  : is_z_isomorphism
      (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx)
  := pr22 F x xx.

Proposition full_comp_cat_fiber_nat_trans_ax
            {C₁ C₂ : full_comp_cat}
            (F : full_comp_cat_functor C₁ C₂)
            (x : C₁)
  : is_nat_trans
      (fiber_functor (comp_cat_comprehension C₁) x
       ∙ fiber_functor (disp_codomain_functor F) x)
      (fiber_functor (comp_cat_type_functor F) x
       ∙ fiber_functor (comp_cat_comprehension C₂) (F x))
      (comp_cat_functor_comprehension F x).
Proof.
  intros xx xx' f.
  use eq_mor_cod_fib.
  refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)).
  cbn -[fiber_functor].
  etrans.
  {
    apply maponpaths_2.
    apply disp_codomain_fiber_functor_mor.
  }
  pose (disp_nat_trans_ax
          (comp_cat_functor_comprehension F)
          (f := identity x)
          (xx := xx')
          (xx' := xx)
          f)
    as p.
  refine (maponpaths (λ z, pr1 z) p @ _).
  refine (transportb_cod_disp _ _ _ @ _).
  cbn.
  apply maponpaths.
  refine (!_).
  apply comprehension_functor_mor_transportf.
Qed.

Definition full_comp_cat_fiber_nat_trans
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (x : C₁)
  : fiber_functor (comp_cat_comprehension C₁) x
    ∙ fiber_functor (disp_codomain_functor F) x
    ⟹
    fiber_functor (comp_cat_type_functor F) x
    ∙ fiber_functor (comp_cat_comprehension C₂) (F x).
Proof.
  use make_nat_trans.
  - exact (comp_cat_functor_comprehension F x).
  - exact (full_comp_cat_fiber_nat_trans_ax F x).
Defined.

Definition full_comp_cat_fiber_nat_z_iso
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (x : C₁)
  : nat_z_iso
      (fiber_functor (comp_cat_comprehension C₁) x
       ∙ fiber_functor (disp_codomain_functor F) x)
      (fiber_functor (comp_cat_type_functor F) x
       ∙ fiber_functor (comp_cat_comprehension C₂) (F x)).
Proof.
  use make_nat_z_iso.
  - exact (full_comp_cat_fiber_nat_trans F x).
  - intro xx.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    apply full_comp_cat_functor_is_z_iso.
Defined.

Definition full_comp_cat_fiber_nat_z_iso_inv
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (x : C₁)
  : nat_z_iso
      (fiber_functor (comp_cat_type_functor F) x
       ∙ fiber_functor (comp_cat_comprehension C₂) (F x))
      (fiber_functor (comp_cat_comprehension C₁) x
       ∙ fiber_functor (disp_codomain_functor F) x)
  := nat_z_iso_inv (full_comp_cat_fiber_nat_z_iso F x).

Definition full_comp_cat_nat_trans
           {C₁ C₂ : full_comp_cat}
           (F G : full_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion full_comp_cat_nat_trans_to_comp_cat_nat_trans
         {C₁ C₂ : full_comp_cat}
         {F G : full_comp_cat_functor C₁ C₂}
         (τ : full_comp_cat_nat_trans F G)
  : comp_cat_nat_trans F G
  := pr1 τ.

Definition make_full_comp_cat_nat_trans
           {C₁ C₂ : full_comp_cat}
           {F G : full_comp_cat_functor C₁ C₂}
           (τ : comp_cat_nat_trans F G)
  : full_comp_cat_nat_trans F G
  := τ ,, tt ,, tt.

Proposition full_comp_nat_trans_eq
            {C₁ C₂ : full_comp_cat}
            {F G : full_comp_cat_functor C₁ C₂}
            {τ₁ τ₂ : full_comp_cat_nat_trans F G}
            (p : ∏ (x : C₁), τ₁ x = τ₂ x)
            (p' := nat_trans_eq (homset_property _) _ _ _ _ p)
            (pp : ∏ (x : C₁)
                    (xx : disp_cat_of_types C₁ x),
                  transportf
                    _
                    (nat_trans_eq_pointwise p' x)
                    (comp_cat_type_nat_trans τ₁ x xx)
                  =
                  comp_cat_type_nat_trans τ₂ x xx)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isapropdirprod ; apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_comprehension_nat_trans_eq.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod ; apply isapropunit.
  }
  use total2_paths_f.
  - use nat_trans_eq.
    {
      apply homset_property.
    }
    exact p.
  - etrans.
    {
      use transportf_dirprod.
    }
    use dirprodeq.
    + simpl.
      rewrite transportf_const.
      apply (proofirrelevance _ (isapropdirprod _ _ isapropunit isapropunit)).
    + simpl.
      use disp_nat_trans_eq.
      intros x xx.
      etrans.
      {
        use disp_nat_trans_transportf.
      }
      apply pp.
Qed.

(** * 4. Adjoint equivalences *)
Definition full_comp_cat_left_adjoint_equivalence_help
           {C₁ C₂ : comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           (x : C₁)
           (xx : disp_cat_of_types C₁ x)
  : is_z_isomorphism
      (comprehension_nat_trans_mor
         (comp_cat_functor_comprehension (pr1 F))
         xx).
Proof.
  revert C₁ C₂ F x xx.
  use J_2_0.
  - exact is_univalent_2_0_bicat_comp_cat.
  - intros C x xx ; cbn.
    apply is_z_isomorphism_identity.
Defined.

Definition full_comp_cat_left_adjoint_equivalence
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence (pr1 F))
  : left_adjoint_equivalence F.
Proof.
  refine (left_adjoint_equivalence_subbicat _ _ _ _ _ _ HF).
  clear C₁ C₂ F HF.
  intros C₁ C₂ HC₁ HC₂ F HF x xx.
  exact (full_comp_cat_left_adjoint_equivalence_help (F ,, HF) x xx).
Defined.
