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

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
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
  - exact (λ C₁ C₂ F, preserves_terminal F).
  - exact (λ C, identity_preserves_terminal _).
  - exact (λ _ _ _ _ _ HF HG, composition_preserves_terminal HF HG).
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

(**
 2. Categories with binary products
 *)
Definition disp_bicat_binprod
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, BinProducts (pr1 C)).
  - exact (λ C₁ C₂ F, preserves_binproduct F).
  - exact (λ C, identity_preserves_binproduct _).
  - exact (λ _ _ _ _ _ HF HG, composition_preserves_binproduct HF HG).
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
  - exact (λ C₁ C₂ F, preserves_pullback F).
  - exact (λ C, identity_preserves_pullback _).
  - exact (λ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
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

Definition univ_cat_with_finlim
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

Definition is_univalent_2_1_univ_cat_with_finlim
  : is_univalent_2_1 univ_cat_with_finlim.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_finlim.
Defined.

Definition is_univalent_2_0_univ_cat_with_finlim
  : is_univalent_2_0 univ_cat_with_finlim.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_finlim.
Defined.

Definition is_univalent_2_univ_cat_with_finlim
  : is_univalent_2 univ_cat_with_finlim.
Proof.
  split.
  - exact is_univalent_2_0_univ_cat_with_finlim.
  - exact is_univalent_2_1_univ_cat_with_finlim.
Defined.

(**
 5. Categories with an initial object
 *)
Definition disp_bicat_initial_obj
  : disp_bicat bicat_of_univ_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Initial (pr1 C)).
  - exact (λ C₁ C₂ F, preserves_initial F).
  - exact (λ C, identity_preserves_initial _).
  - exact (λ _ _ _ _ _ HF HG, composition_preserves_initial HF HG).
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
  - exact (λ C₁ C₂ F, preserves_bincoproduct F).
  - exact (λ C, identity_preserves_bincoproduct _).
  - exact (λ _ _ _ _ _ HF HG, composition_preserves_bincoproduct HF HG).
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
