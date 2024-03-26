(*******************************************************************************************

 The bicategory of categories with a displayed category and a terminal object

 Our goal is to construct the bicategory of full comprehension categories, and to do so, we
 use displayed bicategories. Starting with the bicategory of univalent categories, we add the
 following structure to it in the following order.
 1. A displayed category and a terminal object.
 2. A cleaving for the displayed category.
 3. A comprehension functor.
 4. A proof that this comprehension functor is fully faithful.
 In this file, we look at the first of these.

 To construct the displayed bicategory of displayed categories and terminal objects, we reuse
 constructions already present in UniMath. More specificall, we take the product of two
 displayed bicategories: one of displayed categories and of terminal objects. The univalence
 of this displayed bicategory follows from the univalence of the independent parts.

 Contents
 1. The bicategory of categories with a terminal object and a displayed category
 2. Builders and accessors
 3. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.

Local Open Scope cat.

(** * 1. The bicategory of categories with a terminal object and a displayed category *)
Definition disp_bicat_cat_with_terminal_disp_cat
  : disp_bicat bicat_of_univ_cats
  := disp_dirprod_bicat
       disp_bicat_terminal_obj
       disp_bicat_of_univ_disp_cats.

Proposition disp_univalent_2_1_disp_bicat_cat_with_terminal_disp_cat
  : disp_univalent_2_1 disp_bicat_cat_with_terminal_disp_cat.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
Qed.

Proposition disp_univalent_2_0_disp_bicat_cat_with_terminal_disp_cat
  : disp_univalent_2_0 disp_bicat_cat_with_terminal_disp_cat.
Proof.
  use is_univalent_2_0_dirprod_bicat.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - split.
    + exact disp_univalent_2_0_disp_bicat_of_univ_disp_cat.
    + exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
Qed.

Definition bicat_cat_with_terminal_disp_cat
  : bicat
  := total_bicat disp_bicat_cat_with_terminal_disp_cat.

Proposition is_univalent_2_1_bicat_cat_with_terminal_disp_cat
  : is_univalent_2_1 bicat_cat_with_terminal_disp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_cat_with_terminal_disp_cat.
Qed.

Proposition is_univalent_2_0_bicat_cat_with_terminal_disp_cat
  : is_univalent_2_0 bicat_cat_with_terminal_disp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_cat_with_terminal_disp_cat.
Qed.

Proposition is_univalent_2_bicat_cat_with_terminal_disp_cat
  : is_univalent_2 bicat_cat_with_terminal_disp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_cat_with_terminal_disp_cat.
  - exact is_univalent_2_1_bicat_cat_with_terminal_disp_cat.
Qed.

(** * 2. Builders and accessors *)
Definition cat_with_terminal_disp_cat
  : UU
  := bicat_cat_with_terminal_disp_cat.

Definition make_cat_with_terminal_disp_cat
           (C : univalent_category)
           (T : Terminal C)
           (D : disp_univalent_category C)
  : cat_with_terminal_disp_cat
  := C ,, (T ,, tt) ,, D.

Coercion cat_of_cat_with_terminal_disp_cat
         (C : cat_with_terminal_disp_cat)
  : univalent_category
  := pr1 C.

Definition empty_context
           (C : cat_with_terminal_disp_cat)
  : Terminal C
  := pr112 C.

Definition disp_cat_of_types
           (C : cat_with_terminal_disp_cat)
  : disp_univalent_category C
  := pr22 C.

Definition functor_with_terminal_disp_cat
           (C₁ C₂ : cat_with_terminal_disp_cat)
  : UU
  := C₁ --> C₂.

Definition make_functor_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : C₁ ⟶ C₂)
           (HF : preserves_terminal F)
           (FF : disp_functor F (disp_cat_of_types C₁) (disp_cat_of_types C₂))
  : functor_with_terminal_disp_cat C₁ C₂
  := F ,, (tt ,, HF) ,, FF.

Coercion functor_of_functor_with_terminal_disp_cat
         {C₁ C₂ : cat_with_terminal_disp_cat}
         (F : functor_with_terminal_disp_cat C₁ C₂)
  : C₁ ⟶ C₂
  := pr1 F.

Definition comp_cat_type_functor
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : functor_with_terminal_disp_cat C₁ C₂)
  : disp_functor F (disp_cat_of_types C₁) (disp_cat_of_types C₂)
  := pr22 F.

Definition comp_cat_functor_terminal
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : functor_with_terminal_disp_cat C₁ C₂)
  : preserves_terminal F
  := pr212 F.

Definition nat_trans_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F G : functor_with_terminal_disp_cat C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           {F G : functor_with_terminal_disp_cat C₁ C₂}
           (τ : F ⟹ G)
           (ττ : disp_nat_trans
                   τ
                   (comp_cat_type_functor F)
                   (comp_cat_type_functor G))
  : nat_trans_with_terminal_disp_cat F G
  := τ ,, (tt ,, tt) ,, ττ.

Coercion nat_trans_of_nat_trans_with_terminal_disp_cat
         {C₁ C₂ : cat_with_terminal_disp_cat}
         {F G : functor_with_terminal_disp_cat C₁ C₂}
         (τ : nat_trans_with_terminal_disp_cat F G)
  : F ⟹ G
  := pr1 τ.

Definition comp_cat_type_nat_trans
           {C₁ C₂ : cat_with_terminal_disp_cat}
           {F G : functor_with_terminal_disp_cat C₁ C₂}
           (τ : nat_trans_with_terminal_disp_cat F G)
  : disp_nat_trans τ (comp_cat_type_functor F) (comp_cat_type_functor G)
  := pr22 τ.

(** * 3. Adjoint equivalences *)
Definition cat_with_terminal_disp_cat_left_adjoint_equivalence_help
           {C₁ C₂ : bicat_of_univ_cats}
           (F : adjoint_equivalence C₁ C₂)
           {CC₁ : disp_bicat_cat_with_terminal_disp_cat C₁}
           {CC₂ : disp_bicat_cat_with_terminal_disp_cat C₂}
           (FF : CC₁ -->[ pr1 F ] CC₂)
           (HF₁ := adj_equiv_to_equiv_cat _ F : adj_equivalence_of_cats (pr1 F))
           (A := (_ ,, HF₁) : adj_equiv (pr1 C₁) (pr1 C₂))
           (HF₂ : is_equiv_over A (pr2 FF))
  : left_adjoint_equivalence
      (B := bicat_cat_with_terminal_disp_cat)
      (a := (C₁ ,, CC₁))
      (b := (C₂ ,, CC₂))
      (_ ,, FF).
Proof.
  revert HF₁ A HF₂ ; cbn.
  revert C₁ C₂ F CC₁ CC₂ FF.
  use J_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - intros C₁ CC₁ CC₂ FF HF.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    + apply internal_adjoint_equivalence_identity.
    + use (pair_left_adjoint_equivalence _ _ (internal_adjoint_equivalence_identity C₁)).
      split.
      * apply disp_left_adjoint_equivalence_subbicat_terminal.
      * use disp_left_adjoint_equivalence_disp_bicat_of_univ_cats.
        use is_equiv_over_to_is_equiv_over_id.
        assert (adj_equiv_to_equiv_cat _ (internal_adjoint_equivalence_identity C₁)
                =
                identity_functor_is_adj_equivalence) as p.
        {
          use (proofirrelevance
                 _
                 (isofhlevelweqf
                    1
                    (adj_equiv_is_equiv_cat _)
                    (isaprop_left_adjoint_equivalence _ _))).
          exact univalent_cat_is_univalent_2_1.
        }
        rewrite <- p.
        exact HF.
Qed.

Definition cat_with_terminal_disp_cat_left_adjoint_equivalence
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : functor_with_terminal_disp_cat C₁ C₂)
           (HF₁ : adj_equivalence_of_cats F)
           (A := (_ ,, HF₁) : adj_equiv C₁ C₂)
           (HF₂ : is_equiv_over A (comp_cat_type_functor F))
  : left_adjoint_equivalence F.
Proof.
  use (cat_with_terminal_disp_cat_left_adjoint_equivalence_help
         (_ ,, equiv_cat_to_adj_equiv _ HF₁)
         (pr2 F)).
  cbn.
  assert (adj_equiv_to_equiv_cat _ (equiv_cat_to_adj_equiv _ HF₁) = HF₁) as p.
  {
    use (proofirrelevance
           _
           (isofhlevelweqf
              1
              (adj_equiv_is_equiv_cat _)
              (isaprop_left_adjoint_equivalence _ _))).
    exact univalent_cat_is_univalent_2_1.
  }
  rewrite p.
  exact HF₂.
Qed.
