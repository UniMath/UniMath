(***********************************************************************************

 Bicategories of categories with structure

 We define a number of bicategories whose objects are categories with a certain
 structure and whose 1-cells are functors preserving that structure. The 2-cells
 are just natural transformations.

 Contents
 1. Categories with a terminal object
 2. Categories with binary products
 3. Categories with pullbacks
 4. Categories with finite limits
 5. Categories with an initial object
 6. Categories with binary coproducts
 7. Categories with finite limits and a subobject classifier

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Local Open Scope cat.

(**
 1. Categories with a terminal object
 *)
Definition disp_bicat_terminal_obj
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Terminal (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_terminal F).
  - exact (λ C _, identity_preserves_terminal _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_terminal HF HG).
Defined.

Definition univ_cat_with_terminal_obj
  : bicat
  := total_bicat disp_bicat_terminal_obj.

Definition disp_univalent_2_1_disp_bicat_terminal_obj
  : disp_univalent_2_1 disp_bicat_terminal_obj.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_terminal.
Qed.

Definition disp_univalent_2_0_disp_bicat_terminal_obj
  : disp_univalent_2_0 disp_bicat_terminal_obj.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact univalent_cat_is_univalent_2.
  - intro C.
    apply isaprop_Terminal.
    exact (pr2 C).
  - intros.
    apply isaprop_preserves_terminal.
Qed.

Definition disp_univalent_2_disp_bicat_terminal_obj
  : disp_univalent_2 disp_bicat_terminal_obj.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
Defined.

Definition is_univalent_2_1_univ_cat_with_terminal_obj
  : is_univalent_2_1 univ_cat_with_terminal_obj.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
Defined.

Definition is_univalent_2_0_univ_cat_with_terminal_obj
  : is_univalent_2_0 univ_cat_with_terminal_obj.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_terminal_obj.
Defined.

Definition is_univalent_2_univ_cat_with_terminal_obj
  : is_univalent_2 univ_cat_with_terminal_obj.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_terminal_obj.
  - exact is_univalent_2_1_univ_cat_with_terminal_obj.
Defined.

Proposition disp_left_adjoint_equivalence_subbicat_terminal
            {C₁ C₂ : bicat_of_univ_cats}
            {F : C₁ --> C₂}
            (HF : left_adjoint_equivalence F)
            (T₁ : disp_bicat_terminal_obj C₁)
            (T₂ : disp_bicat_terminal_obj C₂)
            (FT : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FT.
Proof.
  use disp_left_adjoint_equivalence_subbicat.
  - clear C₁ C₂ F HF T₁ T₂ FT ; cbn.
    intros C₁ C₂ T₁ T₂ F HF.
    exact (right_adjoint_preserves_terminal
             _
             (adj_equivalence_of_cats_inv _ (adj_equiv_to_equiv_cat _ HF))).
  - exact univalent_cat_is_univalent_2.
Defined.

(**
 2. Categories with binary products
 *)
Definition disp_bicat_binprod
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, BinProducts (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_binproduct F).
  - exact (λ C _, identity_preserves_binproduct _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_binproduct HF HG).
Defined.

Definition univ_cat_with_binprod
  : bicat
  := total_bicat disp_bicat_binprod.

Definition disp_univalent_2_1_disp_bicat_binprod
  : disp_univalent_2_1 disp_bicat_binprod.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_binproduct.
Qed.

Definition disp_univalent_2_0_disp_bicat_binprod
  : disp_univalent_2_0 disp_bicat_binprod.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact univalent_cat_is_univalent_2.
  - intro C.
    use impred ; intro x.
    use impred ; intro y.
    use isaprop_BinProduct.
    exact (pr2 C).
  - intros.
    apply isaprop_preserves_binproduct.
Defined.

Definition disp_univalent_2_disp_bicat_binprod
  : disp_univalent_2 disp_bicat_binprod.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_binprod.
  - exact disp_univalent_2_1_disp_bicat_binprod.
Defined.

Definition is_univalent_2_1_univ_cat_with_binprod
  : is_univalent_2_1 univ_cat_with_binprod.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_binprod.
Defined.

Definition is_univalent_2_0_univ_cat_with_binprod
  : is_univalent_2_0 univ_cat_with_binprod.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_binprod.
Defined.

Definition is_univalent_2_univ_cat_with_binprod
  : is_univalent_2 univ_cat_with_binprod.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_binprod.
  - exact is_univalent_2_1_univ_cat_with_binprod.
Defined.

(**
 3. Categories with pullbacks
 *)
Definition disp_bicat_pullback
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Pullbacks (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_pullback F).
  - exact (λ C _, identity_preserves_pullback _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
Defined.

Definition univ_cat_with_pb
  : bicat
  := total_bicat disp_bicat_pullback.

Definition disp_univalent_2_1_disp_bicat_pullback
  : disp_univalent_2_1 disp_bicat_pullback.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_pullback.
Qed.

Definition disp_univalent_2_0_disp_bicat_pullback
  : disp_univalent_2_0 disp_bicat_pullback.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact univalent_cat_is_univalent_2.
  - intro C.
    repeat (use impred ; intro).
    apply isaprop_Pullback.
    exact (pr2 C).
  - intros.
    apply isaprop_preserves_pullback.
Qed.

Definition disp_univalent_2_disp_bicat_pullback
  : disp_univalent_2 disp_bicat_pullback.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_pullback.
  - exact disp_univalent_2_1_disp_bicat_pullback.
Defined.

Definition is_univalent_2_1_univ_cat_with_pb
  : is_univalent_2_1 univ_cat_with_pb.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_pullback.
Defined.

Definition is_univalent_2_0_univ_cat_with_pb
  : is_univalent_2_0 univ_cat_with_pb.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_pullback.
Defined.

Definition is_univalent_2_univ_cat_with_pb
  : is_univalent_2 univ_cat_with_pb.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_pb.
  - exact is_univalent_2_1_univ_cat_with_pb.
Defined.

(**
 4. Categories with finite limits
 *)
Definition disp_bicat_finlim
  : disp_bicat bicat_of_univ_cats
  := disp_dirprod_bicat
       disp_bicat_terminal_obj
       disp_bicat_pullback.

Definition bicat_of_univ_cat_with_finlim
  : bicat
  := total_bicat disp_bicat_finlim.

Definition disp_univalent_2_1_disp_bicat_finlim
  : disp_univalent_2_1 disp_bicat_finlim.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_pullback.
Qed.

Definition disp_univalent_2_0_disp_bicat_finlim
  : disp_univalent_2_0 disp_bicat_finlim.
Proof.
  use is_univalent_2_0_dirprod_bicat.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - exact disp_univalent_2_disp_bicat_pullback.
Defined.

Definition disp_univalent_2_disp_bicat_finlim
  : disp_univalent_2 disp_bicat_finlim.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim.
  - exact disp_univalent_2_1_disp_bicat_finlim.
Defined.

Definition is_univalent_2_1_bicat_of_univ_cat_with_finlim
  : is_univalent_2_1 bicat_of_univ_cat_with_finlim.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_finlim.
Defined.

Definition is_univalent_2_0_bicat_of_univ_cat_with_finlim
  : is_univalent_2_0 bicat_of_univ_cat_with_finlim.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_finlim.
Defined.

Definition is_univalent_2_bicat_of_univ_cat_with_finlim
  : is_univalent_2 bicat_of_univ_cat_with_finlim.
Proof.
  split.
  - exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
Defined.

Definition univ_cat_with_finlim
  : UU
  := bicat_of_univ_cat_with_finlim.

Definition make_univ_cat_with_finlim
           (C : univalent_category)
           (T : Terminal C)
           (P : Pullbacks C)
  : univ_cat_with_finlim
  := C ,, (T ,, tt) ,, (P ,, tt).

Coercion univ_cat_of_univ_cat_with_finlim
         (C : univ_cat_with_finlim)
  : univalent_category
  := pr1 C.

Definition terminal_univ_cat_with_finlim
           (C : univ_cat_with_finlim)
  : Terminal C
  := pr112 C.

Definition pullbacks_univ_cat_with_finlim
           (C : univ_cat_with_finlim)
  : Pullbacks C
  := pr122 C.

Definition binproducts_univ_cat_with_finlim
           (C : univ_cat_with_finlim)
  : BinProducts C
  := BinProductsFromPullbacks
       (pullbacks_univ_cat_with_finlim C)
       (terminal_univ_cat_with_finlim C).

Definition functor_finlim
           (C₁ C₂ : univ_cat_with_finlim)
  : UU
  := C₁ --> C₂.

Definition make_functor_finlim
           {C₁ C₂ : univ_cat_with_finlim}
           (F : C₁ ⟶ C₂)
           (FT : preserves_terminal F)
           (FP : preserves_pullback F)
  : functor_finlim C₁ C₂
  := F ,, (tt ,, FT) ,, (tt ,, FP).

Coercion functor_of_functor_finlim
         {C₁ C₂ : univ_cat_with_finlim}
         (F : functor_finlim C₁ C₂)
  : C₁ ⟶ C₂
  := pr1 F.

Definition functor_finlim_preserves_terminal
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
  : preserves_terminal F
  := pr212 F.

Definition functor_finlim_preserves_pullback
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
  : preserves_pullback F
  := pr222 F.

Definition functor_finlim_preserves_binproduct
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
  : preserves_binproduct F
  := preserves_binproduct_from_pullback_terminal
       F
       (terminal_univ_cat_with_finlim C₁)
       (pullbacks_univ_cat_with_finlim C₁)
       (functor_finlim_preserves_pullback F)
       (functor_finlim_preserves_terminal F).

Definition nat_trans_finlim
           {C₁ C₂ : univ_cat_with_finlim}
           (F G : functor_finlim C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_finlim
           {C₁ C₂ : univ_cat_with_finlim}
           {F G : functor_finlim C₁ C₂}
           (τ : F ⟹ G)
  : nat_trans_finlim F G
  := τ ,, (tt ,, tt) ,, (tt ,, tt).

Coercion nat_trans_of_nat_trans_finlim
         {C₁ C₂ : univ_cat_with_finlim}
         {F G : functor_finlim C₁ C₂}
         (τ : nat_trans_finlim F G)
  : F ⟹ G
  := pr1 τ.

Proposition nat_trans_finlim_eq
            {C₁ C₂ : univ_cat_with_finlim}
            {F G : functor_finlim C₁ C₂}
            {τ₁ τ₂ : nat_trans_finlim F G}
            (p : ∏ (x : C₁), τ₁ x = τ₂ x)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isapropdirprod ; use isapropdirprod ; exact isapropunit.
  }
  use nat_trans_eq.
  {
    apply homset_property.
  }
  exact p.
Qed.

Definition is_invertible_2cell_cat_with_finlim
           {C₁ C₂ : univ_cat_with_finlim}
           {F G : functor_finlim C₁ C₂}
           (τ : nat_trans_finlim F G)
           (Hτ : is_nat_z_iso τ)
  : is_invertible_2cell τ.
Proof.
  pose (τiso := (pr1 τ ,, Hτ) : nat_z_iso F G).
  use make_is_invertible_2cell.
  - use make_nat_trans_finlim.
    exact (nat_z_iso_inv τiso).
  - abstract
      (use nat_trans_finlim_eq ;
       intro x ;
       apply (z_iso_inv_after_z_iso (_ ,, Hτ x))).
  - abstract
      (use nat_trans_finlim_eq ;
       intro x ;
       apply (z_iso_after_z_iso_inv (_ ,, Hτ x))).
Defined.

Definition left_adjoint_equivalence_univ_cat_with_finlim
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
           (HF : adj_equivalence_of_cats F)
  : left_adjoint_equivalence F.
Proof.
  use equiv_to_adjequiv.
  simple refine ((_ ,, (_ ,, _)) ,, _ ,, _).
  - use make_functor_finlim.
    + exact (right_adjoint HF).
    + exact (right_adjoint_preserves_terminal _ HF).
    + exact (right_adjoint_preserves_pullback _ HF).
  - use make_nat_trans_finlim.
    exact (unit_nat_z_iso_from_adj_equivalence_of_cats HF).
  - use make_nat_trans_finlim.
    exact (counit_nat_z_iso_from_adj_equivalence_of_cats HF).
  - use is_invertible_2cell_cat_with_finlim.
    apply (unit_nat_z_iso_from_adj_equivalence_of_cats HF).
  - use is_invertible_2cell_cat_with_finlim.
    apply (counit_nat_z_iso_from_adj_equivalence_of_cats HF).
Defined.

(**
 5. Categories with an initial object
 *)
Definition disp_bicat_initial_obj
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Initial (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_initial F).
  - exact (λ C _, identity_preserves_initial _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_initial HF HG).
Defined.

Definition univ_cat_with_initial
  : bicat
  := total_bicat disp_bicat_initial_obj.

Definition disp_univalent_2_1_disp_bicat_initial_obj
  : disp_univalent_2_1 disp_bicat_initial_obj.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_initial.
Qed.

Definition disp_univalent_2_0_disp_bicat_initial_obj
  : disp_univalent_2_0 disp_bicat_initial_obj.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact univalent_cat_is_univalent_2.
  - intro C.
    apply isaprop_Initial.
    exact (pr2 C).
  - intros.
    apply isaprop_preserves_initial.
Qed.

Definition disp_univalent_2_disp_bicat_initial_obj
  : disp_univalent_2 disp_bicat_initial_obj.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_initial_obj.
  - exact disp_univalent_2_1_disp_bicat_initial_obj.
Defined.

Definition is_univalent_2_1_univ_cat_with_initial
  : is_univalent_2_1 univ_cat_with_initial.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_initial_obj.
Defined.

Definition is_univalent_2_0_univ_cat_with_initial
  : is_univalent_2_0 univ_cat_with_initial.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_initial_obj.
Defined.

Definition is_univalent_2_univ_cat_with_initial
  : is_univalent_2 univ_cat_with_initial.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_initial.
  - exact is_univalent_2_1_univ_cat_with_initial.
Defined.

(**
 6. Categories with binary coproducts
 *)
Definition disp_bicat_bincoprod
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, BinCoproducts (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_bincoproduct F).
  - exact (λ C _, identity_preserves_bincoproduct _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_bincoproduct HF HG).
Defined.

Definition univ_cat_with_bincoprod
  : bicat
  := total_bicat disp_bicat_bincoprod.

Definition disp_univalent_2_1_disp_bicat_bincoprod
  : disp_univalent_2_1 disp_bicat_bincoprod.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_bincoproduct.
Qed.

Definition disp_univalent_2_0_disp_bicat_bincoprod
  : disp_univalent_2_0 disp_bicat_bincoprod.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact univalent_cat_is_univalent_2.
  - intro C.
    repeat (use impred ; intro).
    apply isaprop_BinCoproduct.
    exact (pr2 C).
  - intros.
    apply isaprop_preserves_bincoproduct.
Defined.

Definition disp_univalent_2_disp_bicat_bincoprod
  : disp_univalent_2 disp_bicat_bincoprod.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_bincoprod.
  - exact disp_univalent_2_1_disp_bicat_bincoprod.
Defined.

Definition is_univalent_2_1_univ_cat_with_bincoprod
  : is_univalent_2_1 univ_cat_with_bincoprod.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_bincoprod.
Defined.

Definition is_univalent_2_0_univ_cat_with_bincoprod
  : is_univalent_2_0 univ_cat_with_bincoprod.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_bincoprod.
Defined.

Definition is_univalent_2_univ_cat_with_bincoprod
  : is_univalent_2 univ_cat_with_bincoprod.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_bincoprod.
  - exact is_univalent_2_1_univ_cat_with_bincoprod.
Defined.

(**
 7. Categories with finite limits and a subobject classifier
 *)
Definition disp_bicat_finlim_subobject_classifier
  : disp_bicat bicat_of_univ_cat_with_finlim.
Proof.
  use disp_subbicat.
  - exact (λ (C : univ_cat_with_finlim),
           subobject_classifier (terminal_univ_cat_with_finlim C)).
  - exact (λ (C₁ C₂ : univ_cat_with_finlim)
             (Ω₁ : subobject_classifier
                     (terminal_univ_cat_with_finlim C₁))
             (Ω₂ : subobject_classifier
                     (terminal_univ_cat_with_finlim C₂))
             (F : functor_finlim C₁ C₂),
           preserves_subobject_classifier
             F
             (terminal_univ_cat_with_finlim C₁)
             (terminal_univ_cat_with_finlim C₂)
             (functor_finlim_preserves_terminal F)).
  - intros.
    apply identity_preserves_subobject_classifier.
  - intros C₁ C₂ C₃ Ω₁ Ω₂ Ω₃ F G HF HG.
    exact (comp_preserves_subobject_classifier HF HG).
Defined.

Definition bicat_of_univ_cat_with_finlim_subobject_classifier
  : bicat
  := total_bicat disp_bicat_finlim_subobject_classifier.

Definition disp_univalent_2_1_disp_bicat_finlim_subobject_classifier
  : disp_univalent_2_1 disp_bicat_finlim_subobject_classifier.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_preserves_subobject_classifier.
Qed.

Definition disp_univalent_2_0_disp_bicat_finlim_subobject_classifier
  : disp_univalent_2_0 disp_bicat_finlim_subobject_classifier.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - intro C.
    apply isaprop_subobject_classifier.
  - intros.
    apply isaprop_preserves_subobject_classifier.
Qed.

Definition disp_univalent_2_disp_bicat_finlim_subobject_classifier
  : disp_univalent_2 disp_bicat_finlim_subobject_classifier.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim_subobject_classifier.
  - exact disp_univalent_2_1_disp_bicat_finlim_subobject_classifier.
Defined.

Definition disp_2cells_isaprop_finlim_subobject_classifier
  : disp_2cells_isaprop disp_bicat_finlim_subobject_classifier.
Proof.
  apply disp_2cells_isaprop_subbicat.
Defined.

Definition disp_locally_groupoid_finlim_subobject_classifier
  : disp_locally_groupoid disp_bicat_finlim_subobject_classifier.
Proof.
  apply disp_locally_groupoid_subbicat.
  exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Defined.

Definition disp_2cells_iscontr_finlim_subobject_classifier
  : disp_2cells_iscontr disp_bicat_finlim_subobject_classifier.
Proof.
  apply disp_2cells_iscontr_subbicat.
Defined.

Definition is_univalent_2_1_bicat_of_univ_cat_with_finlim_subobject_classifier
  : is_univalent_2_1 bicat_of_univ_cat_with_finlim_subobject_classifier.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
  - exact disp_univalent_2_1_disp_bicat_finlim_subobject_classifier.
Defined.

Definition is_univalent_2_0_bicat_of_univ_cat_with_finlim_subobject_classifier
  : is_univalent_2_0 bicat_of_univ_cat_with_finlim_subobject_classifier.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
  - exact disp_univalent_2_0_disp_bicat_finlim_subobject_classifier.
Defined.

Definition is_univalent_2_bicat_of_univ_cat_with_finlim_subobject_classifier
  : is_univalent_2 bicat_of_univ_cat_with_finlim_subobject_classifier.
Proof.
  split.
  - exact is_univalent_2_0_bicat_of_univ_cat_with_finlim_subobject_classifier.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim_subobject_classifier.
Defined.

Definition univ_cat_with_finlim_subobject_classifier
  : UU
  := bicat_of_univ_cat_with_finlim_subobject_classifier.

Definition make_univ_cat_with_finlim_subobject_classifier
           (C : univ_cat_with_finlim)
           (Ω : subobject_classifier (terminal_univ_cat_with_finlim C))
  : univ_cat_with_finlim_subobject_classifier
  := C ,, (Ω ,, tt).

Coercion univ_cat_with_finlim_subobject_classifier_to_finlim
         (C : univ_cat_with_finlim_subobject_classifier)
  : univ_cat_with_finlim
  := pr1 C.

Definition subobject_classifier_of_cat
           (C : univ_cat_with_finlim_subobject_classifier)
  : subobject_classifier (terminal_univ_cat_with_finlim C)
  := pr12 C.

Definition functor_finlim_subobject_classifier
           (C₁ C₂ : univ_cat_with_finlim_subobject_classifier)
  : UU
  := C₁ --> C₂.

Definition make_functor_finlim_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           (F : functor_finlim C₁ C₂)
           (HF : preserves_subobject_classifier
                   F
                   (terminal_univ_cat_with_finlim C₁)
                   (terminal_univ_cat_with_finlim C₂)
                   (functor_finlim_preserves_terminal F))
  : functor_finlim_subobject_classifier C₁ C₂
  := F ,, (tt ,, HF).

Coercion functor_finlim_of_functor_finlim_subobject_classifier
         {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
         (F : functor_finlim_subobject_classifier C₁ C₂)
  : functor_finlim C₁ C₂
  := pr1 F.

Definition functor_finlim_preserves_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           (F : functor_finlim_subobject_classifier C₁ C₂)
  : preserves_subobject_classifier
      F
      (terminal_univ_cat_with_finlim C₁)
      (terminal_univ_cat_with_finlim C₂)
      (functor_finlim_preserves_terminal F)
  := pr22 F.

Definition nat_trans_finlim_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           (F G : functor_finlim_subobject_classifier C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_finlim_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           {F G : functor_finlim_subobject_classifier C₁ C₂}
           (τ : nat_trans_finlim F G)
  : nat_trans_finlim_subobject_classifier F G
  := τ ,, (tt ,, tt).

Coercion nat_trans_finlim_of_subobject_classifier
         {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
         {F G : functor_finlim_subobject_classifier C₁ C₂}
         (τ : nat_trans_finlim_subobject_classifier F G)
  : nat_trans_finlim F G
  := pr1 τ.

Proposition nat_trans_finlim_subobject_classifier_eq
            {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
            {F G : functor_finlim_subobject_classifier C₁ C₂}
            {τ₁ τ₂ : nat_trans_finlim_subobject_classifier F G}
            (p : ∏ (x : C₁), τ₁ x = τ₂ x)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isapropdirprod ; exact isapropunit.
  }
  use nat_trans_finlim_eq.
  exact p.
Qed.

Definition is_invertible_2cell_cat_with_finlim_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           {F G : functor_finlim_subobject_classifier C₁ C₂}
           (τ : nat_trans_finlim_subobject_classifier F G)
           (Hτ : is_nat_z_iso τ)
  : is_invertible_2cell τ.
Proof.
  pose (τiso := (pr11 τ ,, Hτ) : nat_z_iso F G).
  use make_is_invertible_2cell.
  - use make_nat_trans_finlim_subobject_classifier.
    use make_nat_trans_finlim.
    exact (nat_z_iso_inv τiso).
  - abstract
      (use nat_trans_finlim_subobject_classifier_eq ;
       intro x ;
       apply (z_iso_inv_after_z_iso (_ ,, Hτ x))).
  - abstract
      (use nat_trans_finlim_subobject_classifier_eq ;
       intro x ;
       apply (z_iso_after_z_iso_inv (_ ,, Hτ x))).
Defined.

Definition adj_equiv_preserves_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim}
           (Ω₁ : subobject_classifier (terminal_univ_cat_with_finlim C₁))
           (Ω₂ : subobject_classifier (terminal_univ_cat_with_finlim C₂))
           (F : adjoint_equivalence C₁ C₂)
  : preserves_subobject_classifier
      (pr1 F : functor_finlim C₁ C₂)
      (terminal_univ_cat_with_finlim C₁)
      (terminal_univ_cat_with_finlim C₂)
      (functor_finlim_preserves_terminal (pr1 F)).
Proof.
  revert C₁ C₂ F Ω₁ Ω₂.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
  }
  intros C Ω₁ Ω₂.
  apply identity_preserves_subobject_classifier.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_univ_cat_subobject_classifier
           {C₁ C₂ : bicat_of_univ_cat_with_finlim}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_finlim_subobject_classifier C₁}
           {T₂ : disp_bicat_finlim_subobject_classifier C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  use disp_left_adjoint_equivalence_subbicat_alt.
  exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Definition left_adjoint_equivalence_univ_cat_with_finlim_subobject_classifier
           {C₁ C₂ : univ_cat_with_finlim_subobject_classifier}
           (F : functor_finlim_subobject_classifier C₁ C₂)
           (HF : adj_equivalence_of_cats F)
  : left_adjoint_equivalence F.
Proof.
  use left_adjoint_equivalence_subbicat.
  - clear C₁ C₂ F HF.
    intros C₁ C₂ Ω₁ Ω₂ F HF.
    exact (adj_equiv_preserves_subobject_classifier Ω₁ Ω₂ (F ,, HF)).
  - use left_adjoint_equivalence_univ_cat_with_finlim.
    exact HF.
Defined.
