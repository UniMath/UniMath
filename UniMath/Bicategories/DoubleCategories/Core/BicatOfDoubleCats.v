(**********************************************************************************

 The Bicategory of Double Categories

 In this file, we define the bicategory of univalent double categories, and we
 prove that this bicategory is univalent. To do so, we make heavy use of the
 machinery of displayed bicategories.

 The idea behind this construction is to split up the notion of double category into
 several layers. More specifically, a univalent double category is a
 univalent category with another collection of morphisms and a collection of squares.
 As such, the starting point of this construction is the univalent bicategory of
 univalent categories.

 First, we add the collection of morphisms and squares to the structure, which is
 done by a 2-sided displayed category. This construction is defined in the file
 `DispBicatOfTwoSidedDispCat.v` where it is also proven that this gives rise to a
 univalent bicategory.

 Next, there are two pieces of data to add: identity morphisms and horizontal
 composition. So, we define two displayed bicategories on top of the bicategory of
 categories with a 2-sided displayed category
 - The displayed objects of the first one are horizontal identities, the displayed
   morphisms are squares that witness the lax preservation of identities, and the
   displayed 2-cells are coherences (i.e., the coherence for horizontal identities
   for double transformations).
 - The displayed objects of the first one are functions that take horizontal
   compositions, the displayed morphisms are squares that witness the lax
   preservation of composition, and the displayed 2-cells are coherences (i.e., the
   coherence for horizontal composition for double transformations).
 We take the product of these two displayed bicategories, and we continue with the
 resulting total bicategory. While the 2-cells in this bicategory are double
 transformations, we need to add more structure in order to get double categories
 as objects and double functors as morphisms.

 As such, we define three displayed bicategories on top of that total bicategory.
 - The displayed objects of the first one are left unitors, and the displayed
   morphisms are coherences (i.e., the coherence equation for left unitors by
   double functors).
 - The displayed objects of the first one are right unitors, and the displayed
   morphisms are coherences (i.e., the coherence equation for right unitors by
   double functors).
 - The displayed objects of the first one are associator, and the displayed
   morphisms are coherences (i.e., the coherence equation for associator by
   double functors).
 Again we take the product of these three displayed bicategories, and we look
 at the resulting total bicategory. The 1-cells are double functors and the 2-cells
 are double transformations. However, the objects are not yet double categories:
 the triangle and pentagon coherence are missing.

 We finish the construction by taking a full subbicategory where the condition that
 we require is precisely the triangle and the pentagon equation. As a consequence,
 the objects of the resulting bicategory are actually double categories.

 In every step, we also prove the displayed univalence of the involved displayed
 bicategories. This allows us to prove in the end that the bicategory of double
 categories is a univalent bicategory.

 Contents
 1. Two-sided displayed categories with identities
 2. Two-sided displayed categories with horizontal composition
 3. Two-sided displayed categories with identities and horizontal composition
 4. Two-sided displayed categories with left unitors
 5. Two-sided displayed categories with right unitors
 6. Two-sided displayed categories with associators
 7. Two-sided displayed categories with unitors and associators
 8. Displayed bicategory of double categories

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfTwoSidedDispCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleTransformation.

Local Open Scope cat.

(** * 1. Two-sided displayed categories with identities *)
Definition disp_cat_ob_mor_twosided_disp_cat_hor_id
  : disp_cat_ob_mor bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, hor_id (pr12 CD)).
  - exact (λ CD₁ CD₂ I₁ I₂ FFF, double_functor_hor_id (pr2 FFF) I₁ I₂).
Defined.

Definition disp_cat_id_comp_twosided_disp_cat_hor_id
  : disp_cat_id_comp
      bicat_twosided_disp_cat
      disp_cat_ob_mor_twosided_disp_cat_hor_id.
Proof.
  split.
  - exact (λ C I, identity_hor_id I).
  - exact (λ C₁ C₂ C₃ FFF GGG I₁ I₂ I₃ FI GI, comp_hor_id FI GI).
Defined.

Definition disp_cat_data_twosided_disp_cat_hor_id
  : disp_cat_data bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_twosided_disp_cat_hor_id.
  - exact disp_cat_id_comp_twosided_disp_cat_hor_id.
Defined.

Definition disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_id
  : disp_prebicat_1_id_comp_cells bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_twosided_disp_cat_hor_id.
  - exact (λ CD₁ CD₂ FFF GGG τττ I₁ I₂ FI GI, double_nat_trans_hor_id (pr2 τττ) FI GI).
Defined.

Definition disp_prebicat_1_ops_twosided_disp_cat_hor_id
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_id.
Proof.
  repeat split.
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (id_twosided_disp_nat_trans_hor_id IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (lunitor_twosided_disp_nat_trans_hor_id IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (runitor_twosided_disp_nat_trans_hor_id IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (linvunitor_twosided_disp_nat_trans_hor_id IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (rinvunitor_twosided_disp_nat_trans_hor_id IF).
  - intros CD₁ CD₂ CD₃ CD₄ F G H I₁ I₂ I₃ I₄ IF IG IH.
    exact (rassociator_twosided_disp_nat_trans_hor_id IF IG IH).
  - intros CD₁ CD₂ CD₃ CD₄ F G H I₁ I₂ I₃ I₄ IF IG IH.
    exact (lassociator_twosided_disp_nat_trans_hor_id IF IG IH).
  - intros CD₁ CD₂ F G H τ θ I₁ I₂ IF IG IH Iτ Iθ ; cbn.
    exact (comp_twosided_disp_nat_trans_hor_id Iτ Iθ).
  - intros CD₁ CD₂ CD₃ F G₁ G₂ θ I₁ I₂ I₃ IF IG₁ IG₂ Iθ.
    exact (pre_whisker_twosided_disp_nat_trans_hor_id IF Iθ).
  - intros CD₁ CD₂ CD₃ F G₁ G₂ τ I₁ I₂ I₃ IF₁ IF₂ IG Iτ.
    exact (post_whisker_twosided_disp_nat_trans_hor_id IG Iτ).
Qed.

Definition disp_prebicat_data_twosided_disp_cat_hor_id
  : disp_prebicat_data bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_id.
  - exact disp_prebicat_1_ops_twosided_disp_cat_hor_id.
Defined.

Proposition disp_prebicat_laws_twosided_disp_cat_hor_id
  : disp_prebicat_laws disp_prebicat_data_twosided_disp_cat_hor_id.
Proof.
  repeat split ; intro ; intros ; apply isaprop_double_nat_trans_hor_id.
Qed.

Definition disp_prebicat_twosided_disp_cat_hor_id
  : disp_prebicat bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_twosided_disp_cat_hor_id.
  - exact disp_prebicat_laws_twosided_disp_cat_hor_id.
Defined.

Definition disp_bicat_twosided_disp_cat_hor_id
  : disp_bicat bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_twosided_disp_cat_hor_id.
  - intro ; intros.
    apply isasetaprop.
    apply isaprop_double_nat_trans_hor_id.
Defined.

Definition isaprop_disp_2cell_hor_id
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F : CD₁ --> CD₂}
           {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
           {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
           {FI GI : I₁ -->[ F] I₂}
           (τ τ' : FI ==>[ id2 _ ] GI)
  : τ = τ'.
Proof.
  apply isaprop_double_nat_trans_hor_id.
Qed.

Definition is_disp_invertible_2cell_hor_id_over_id
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F : CD₁ --> CD₂}
           {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
           {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
           {FI GI : I₁ -->[ F] I₂}
           (τ : FI ==>[ id2 _ ] GI)
  : is_disp_invertible_2cell
      (id2_invertible_2cell F)
      τ.
Proof.
  simple refine (_ ,, _ ,, _).
  - intros x ; cbn.
    pose (p := τ x) ; cbn in p.
    rewrite id_two_disp_right.
    rewrite id_two_disp_right in p.
    rewrite double_id_mor_id.
    rewrite double_id_mor_id in p.
    rewrite id_two_disp_left.
    rewrite id_two_disp_left in p.
    rewrite transport_b_b_disp_mor2.
    rewrite transport_b_b_disp_mor2 in p.
    refine (_ @ !p @ _) ; use transportf_disp_mor2_eq ; apply idpath.
  - apply isaprop_double_nat_trans_hor_id.
  - apply isaprop_double_nat_trans_hor_id.
Qed.

Definition is_disp_invertible_2cell_hor_id
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F G : CD₁ --> CD₂}
           {τ : invertible_2cell F G}
           {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
           {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
           {FI : I₁ -->[ F ] I₂}
           {GI : I₁ -->[ G ] I₂}
           (ττ : FI ==>[ τ ] GI)
  : is_disp_invertible_2cell τ ττ.
Proof.
  revert CD₁ CD₂ F G τ I₁ I₂ FI GI ττ.
  use J_2_1.
  - apply is_univalent_2_1_bicat_twosided_disp_cat.
  - cbn.
    intro ; intros.
    apply is_disp_invertible_2cell_hor_id_over_id.
Qed.

Section HorIdDispInv2cell.
  Context {CD₁ CD₂ : bicat_twosided_disp_cat}
          {F : CD₁ --> CD₂}
          {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
          {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
          (FI GI : I₁ -->[ F] I₂).

  Definition disp_bicat_twosided_disp_cat_hor_id_weq_inv2cell
    : pr1 FI ~ pr1 GI
      ≃
      disp_invertible_2cell (id2_invertible_2cell F) FI GI.
  Proof.
    use weqimplimpl.
    - intro p.
      simple refine (_ ,, _).
      + intro x ; cbn.
        rewrite id_two_disp_right.
        rewrite double_id_mor_id.
        rewrite id_two_disp_left.
        rewrite transport_b_b_disp_mor2.
        etrans.
        {
          apply maponpaths.
          exact (p x).
        }
        use transportf_disp_mor2_eq.
        apply idpath.
      + apply is_disp_invertible_2cell_hor_id.
    - intros p x.
      pose (q := pr1 p x).
      cbn in q.
      rewrite id_two_disp_right in q.
      rewrite double_id_mor_id in q.
      rewrite id_two_disp_left in q.
      rewrite transport_b_b_disp_mor2 in q.
      refine (!_ @ maponpaths _ q @ transportfb_disp_mor2 _ _ _).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
    - use impred ; intro.
      apply isaset_disp_mor.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
      + intros.
        apply isaprop_double_nat_trans_hor_id.
  Qed.
End HorIdDispInv2cell.

Definition disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2_1 disp_bicat_twosided_disp_cat_hor_id.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros CD₁ CD₂ F I₁ I₂ FI GI.
  use weqhomot.
  - refine (disp_bicat_twosided_disp_cat_hor_id_weq_inv2cell FI GI
            ∘ weqtoforallpaths _ _ _
            ∘ path_sigma_hprop _ _ _ _)%weq.
    apply isaprop_double_functor_hor_id_laws.
  - intro p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_disp_invertible_2cell.
    }
    apply isaprop_double_nat_trans_hor_id.
Qed.

Section AdjEquivHorId.
  Context {CD : bicat_twosided_disp_cat}
          (FF GG : disp_bicat_twosided_disp_cat_hor_id CD)
          (τ : FF -->[ identity CD ] GG)
          (Hτ : ∏ (x : pr11 CD),
                is_iso_twosided_disp
                  (identity_is_z_iso _)
                  (identity_is_z_iso _)
                  (pr1 τ x)).

  Definition to_disp_left_adjequiv_hor_id_inv_data
    : double_functor_hor_id_data (twosided_disp_functor_identity _) GG FF
    := λ x, pr1 (Hτ x).

  Arguments to_disp_left_adjequiv_hor_id_inv_data /.

  Proposition to_disp_left_adjequiv_hor_id_inv_laws
    : double_functor_hor_id_laws to_disp_left_adjequiv_hor_id_inv_data.
  Proof.
    intros x y f ; cbn.
    pose (pr2 τ x y f) as p ; cbn in p.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply id_two_disp_right_alt.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 3 apply maponpaths.
      exact (inv_after_iso_twosided_disp_alt (Hτ y)).
    }
    rewrite !two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite assoc_two_disp.
      apply maponpaths.
      apply maponpaths_2.
      exact (pr2 τ x y f).
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite !assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    apply transportf_disp_mor2_idpath.
  Qed.

  Definition to_disp_left_adjequiv_hor_id_inv
    : double_functor_hor_id (twosided_disp_functor_identity _) GG FF.
  Proof.
    use make_double_functor_hor_id.
    - exact to_disp_left_adjequiv_hor_id_inv_data.
    - exact to_disp_left_adjequiv_hor_id_inv_laws.
  Defined.

  Proposition to_disp_left_adjequiv_hor_id_unit
    : double_nat_trans_hor_id
        (id_twosided_disp_nat_trans (twosided_disp_functor_identity _))
        (identity_hor_id FF)
        (comp_hor_id τ to_disp_left_adjequiv_hor_id_inv).
  Proof.
    intros x ; cbn.
    rewrite id_two_disp_left.
    rewrite two_disp_post_whisker_f.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite double_id_mor_id.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    use transportf_disp_mor2_eq.
    apply idpath.
  Qed.

  Proposition to_disp_left_adjequiv_hor_id_counit
    : double_nat_trans_hor_id
        (id_twosided_disp_nat_trans (twosided_disp_functor_identity _))
        (comp_hor_id to_disp_left_adjequiv_hor_id_inv τ)
        (identity_hor_id GG).
  Proof.
    intros x ; cbn.
    rewrite !id_two_disp_right.
    unfold transportb_disp_mor2.
    rewrite !transport_f_f_disp_mor2.
    rewrite double_id_mor_id.
    etrans.
    {
      apply maponpaths.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    use transportf_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition to_disp_left_adjequiv_hor_id
    : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity CD) τ.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
    - exact to_disp_left_adjequiv_hor_id_inv.
    - exact to_disp_left_adjequiv_hor_id_unit.
    - exact to_disp_left_adjequiv_hor_id_counit.
    - apply isaprop_double_nat_trans_hor_id.
    - apply isaprop_double_nat_trans_hor_id.
    - apply is_disp_invertible_2cell_hor_id.
    - apply is_disp_invertible_2cell_hor_id.
  Qed.
End AdjEquivHorId.

Definition weq_disp_left_adjequiv_hor_id_map
           {CD : bicat_twosided_disp_cat}
           {FF GG : disp_bicat_twosided_disp_cat_hor_id CD}
           (τ : ∏ (x : pr11 CD),
                iso_twosided_disp
                  (identity_z_iso x) (identity_z_iso x)
                  (double_id (pr1 GG) x) (double_id (pr1 FF) x))
           (Hτ : double_functor_hor_id_laws
                   (FF := twosided_disp_functor_identity _)
                   (I₁ := FF) (I₂ := GG)
                   (λ x, pr1 (τ x)))
  : disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG.
Proof.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact (λ x, τ x).
    + exact Hτ.
  - use to_disp_left_adjequiv_hor_id.
    intro x.
    exact (pr2 (τ x)).
Defined.

Definition disp_left_adjequiv_hor_id_help
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           (F : adjoint_equivalence CD₁ CD₂)
           {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
           {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
           (τ : I₁ -->[ F ] I₂)
           (Hτ : ∏ (x : pr11 CD₁),
                 is_iso_twosided_disp
                   (identity_is_z_iso _)
                   (identity_is_z_iso _)
                   (pr1 τ x))
  : disp_left_adjoint_equivalence F τ.
Proof.
  revert CD₁ CD₂ F I₁ I₂ τ Hτ.
  use J_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat.
  - intros CD I₁ I₂ τ Hτ.
    use to_disp_left_adjequiv_hor_id.
    exact Hτ.
Qed.

Definition disp_left_adjequiv_hor_id
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F : CD₁ --> CD₂}
           (HF : left_adjoint_equivalence F)
           {I₁ : disp_bicat_twosided_disp_cat_hor_id CD₁}
           {I₂ : disp_bicat_twosided_disp_cat_hor_id CD₂}
           (τ : I₁ -->[ F ] I₂)
           (Hτ : ∏ (x : pr11 CD₁),
                 is_iso_twosided_disp
                   (identity_is_z_iso _)
                   (identity_is_z_iso _)
                   (pr1 τ x))
  : disp_left_adjoint_equivalence HF τ.
Proof.
  exact (disp_left_adjequiv_hor_id_help (F ,, HF) τ Hτ).
Qed.

Section FromAdjEquivHorId.
  Context {CD : bicat_twosided_disp_cat}
          {FF GG : disp_bicat_twosided_disp_cat_hor_id CD}
          (τ : disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG).

  Definition weq_disp_left_adjequiv_hor_id_inv_iso
             (x : pr11 CD)
    : is_iso_twosided_disp (identity_is_z_iso x) (identity_is_z_iso x) ((pr11 τ) x).
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 (pr112 τ) x).
    - split.
      + abstract
          (cbn ;
           pose (p := pr2 (pr212 τ) x) ;
           cbn in p ;
           rewrite id_two_disp_right in p ;
           rewrite double_id_mor_id in p ;
           rewrite id_two_disp_left in p ;
           unfold transportb_disp_mor2 in p ;
           rewrite !transport_f_f_disp_mor2 in p ;
           refine (!(transportbf_disp_mor2 _ _ _) @ maponpaths _ p @ _) ;
           unfold transportb_disp_mor2 ;
           rewrite transport_f_f_disp_mor2 ;
           use transportf_disp_mor2_eq ;
           apply idpath).
      + abstract
          (pose (p := pr1 (pr212 τ) x) ;
           cbn in p ;
           rewrite id_two_disp_left in p ;
           rewrite double_id_mor_id in p ;
           rewrite id_two_disp_left in p ;
           unfold transportb_disp_mor2 in p ;
           rewrite !transport_f_f_disp_mor2 in p ;
           refine (!(transportbf_disp_mor2 _ _ _) @ maponpaths _ (!p) @ _) ;
           unfold transportb_disp_mor2 ;
           rewrite transport_f_f_disp_mor2 ;
           use transportf_disp_mor2_eq ;
           apply idpath).
  Defined.

  Proposition weq_disp_left_adjequiv_hor_id_inv_laws
    : double_functor_hor_id_laws
        (FF := twosided_disp_functor_identity _)
        (I₁ := FF) (I₂ := GG)
        (λ x, pr11 τ x).
  Proof.
    intros x y f.
    exact (pr21 τ x y f).
  Qed.
End FromAdjEquivHorId.

Definition weq_disp_left_adjequiv_hor_id_inv
           {CD : bicat_twosided_disp_cat}
           {FF GG : disp_bicat_twosided_disp_cat_hor_id CD}
           (τ : disp_adjoint_equivalence
                  (internal_adjoint_equivalence_identity CD)
                  FF GG)
  : ∑ (F : ∏ (x : pr11 CD),
           iso_twosided_disp
             (identity_z_iso x) (identity_z_iso x)
             (double_id (pr1 GG) x) (double_id (pr1 FF) x)),
    double_functor_hor_id_laws
      (FF := twosided_disp_functor_identity _)
      (I₁ := FF) (I₂ := GG)
      (λ x, pr1 (F x)).
Proof.
  simple refine (_ ,, _).
  - intro x.
    simple refine (_ ,, _).
    + exact (pr11 τ x).
    + exact (weq_disp_left_adjequiv_hor_id_inv_iso τ x).
  - exact (weq_disp_left_adjequiv_hor_id_inv_laws τ).
Defined.

Definition weq_disp_left_adjequiv_hor_id
           {CD : bicat_twosided_disp_cat}
           (FF GG : disp_bicat_twosided_disp_cat_hor_id CD)
  : (∑ (F : ∏ (x : pr11 CD),
            iso_twosided_disp
              (identity_z_iso x) (identity_z_iso x)
              (double_id (pr1 GG) x) (double_id (pr1 FF) x)),
      double_functor_hor_id_laws
        (FF := twosided_disp_functor_identity _)
        (I₁ := FF) (I₂ := GG)
        (λ x, pr1 (F x)))
    ≃
    disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG.
Proof.
  use weq_iso.
  - intros F.
    exact (weq_disp_left_adjequiv_hor_id_map (pr1 F) (pr2 F)).
  - exact weq_disp_left_adjequiv_hor_id_inv.
  - abstract
      (intro τ ;
       use subtypePath ; [ intro ; apply isaprop_double_functor_hor_id_laws | ] ;
       use funextsec ; intro ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
       cbn ;
       apply idpath).
  - abstract
      (intro τ ;
       use subtypePath ;
       [ intro ;
         apply isaprop_disp_left_adjoint_equivalence ;
         [ apply is_univalent_2_1_bicat_twosided_disp_cat
         | apply disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id ]
       | ] ;
       use subtypePath ; [ intro ; apply isaprop_double_functor_hor_id_laws | ] ;
       use funextsec ; intro ;
       cbn ;
       apply idpath).
Defined.

Definition disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2_0 disp_bicat_twosided_disp_cat_hor_id.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros CD FF GG.
  use weqhomot.
  - refine (weq_disp_left_adjequiv_hor_id FF GG
            ∘ weqtotal2
                (weqonsecfibers
                   _ _
                   (λ x,
                    make_weq _ (pr22 CD _ _ _ _ (idpath _) (idpath _) (pr11 GG x) (pr11 FF x))
                    ∘ weqpathsinv0 _ _)
                 ∘ weqtoforallpaths _ _ _)
                _
            ∘ total2_paths_equiv _ _ _
            ∘ path_sigma_hprop _ _ _ (isaprop_hor_id_laws _))%weq.
    induction FF as [ [ FF₁ FF₂ ] H ].
    induction GG as [ [ GG₁ GG₂ ] K ].
    intro p.
    pose (q := p : FF₁ = GG₁).
    assert (p = q) by apply idpath.
    induction q.
    rewrite X ; clear p X.
    cbn.
    use weqimplimpl.
    + intro q.
      intros x y f.
      cbn.
      rewrite q.
      rewrite id_two_disp_left.
      rewrite id_two_disp_right.
      rewrite transport_b_b_disp_mor2.
      use transportf_disp_mor2_eq.
      apply idpath.
    + intro q.
      use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro f.
      pose (q x y f) as p.
      cbn in p.
      rewrite id_two_disp_left in p.
      rewrite id_two_disp_right in p.
      rewrite transport_b_b_disp_mor2 in p.
      refine (!(transportfb_disp_mor2 _ _ _) @ maponpaths _ (!p) @ _).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
    + do 3 (use impred_isaset ; intro).
      apply isaset_disp_mor.
    + apply isaprop_double_functor_hor_id_laws.
  - intro p.
    cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence.
      - apply is_univalent_2_1_bicat_twosided_disp_cat.
      - apply disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_double_functor_hor_id_laws.
    }
    cbn.
    apply idpath.
Qed.

Definition disp_univalent_2_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2 disp_bicat_twosided_disp_cat_hor_id.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_id.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id.
Qed.

(** * 2. Two-sided displayed categories with horizontal composition *)
Definition disp_cat_ob_mor_twosided_disp_cat_hor_comp
  : disp_cat_ob_mor bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, hor_comp (pr12 CD)).
  - exact (λ CD₁ CD₂ Cm₁ Cm₂ FFF, double_functor_hor_comp (pr2 FFF) Cm₁ Cm₂).
Defined.

Definition disp_cat_id_comp_twosided_disp_cat_hor_comp
  : disp_cat_id_comp
      bicat_twosided_disp_cat
      disp_cat_ob_mor_twosided_disp_cat_hor_comp.
Proof.
  split.
  - exact (λ C Cm, identity_hor_comp Cm).
  - exact (λ C₁ C₂ C₃ FFF GGG Cm₁ Cm₂ Cm₃ FC GC, comp_hor_comp FC GC).
Defined.

Definition disp_cat_data_twosided_disp_cat_hor_comp
  : disp_cat_data bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_twosided_disp_cat_hor_comp.
  - exact disp_cat_id_comp_twosided_disp_cat_hor_comp.
Defined.

Definition disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_comp
  : disp_prebicat_1_id_comp_cells bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_twosided_disp_cat_hor_comp.
  - exact (λ CD₁ CD₂ FFF GGG τττ I₁ I₂ FC GC, double_nat_trans_hor_comp (pr2 τττ) FC GC).
Defined.

Definition disp_prebicat_1_ops_twosided_disp_cat_hor_comp
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_comp.
Proof.
  repeat split.
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (id_twosided_disp_nat_trans_hor_comp IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (lunitor_twosided_disp_nat_trans_hor_comp IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (runitor_twosided_disp_nat_trans_hor_comp IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (linvunitor_twosided_disp_nat_trans_hor_comp IF).
  - intros CD₁ CD₂ F I₁ I₂ IF.
    exact (rinvunitor_twosided_disp_nat_trans_hor_comp IF).
  - intros CD₁ CD₂ CD₃ CD₄ F G H I₁ I₂ I₃ I₄ IF IG IH.
    exact (rassociator_twosided_disp_nat_trans_hor_comp IF IG IH).
  - intros CD₁ CD₂ CD₃ CD₄ F G H I₁ I₂ I₃ I₄ IF IG IH.
    exact (lassociator_twosided_disp_nat_trans_hor_comp IF IG IH).
  - intros CD₁ CD₂ F G H τ θ I₁ I₂ IF IG IH Iτ Iθ ; cbn.
    exact (comp_twosided_disp_nat_trans_hor_comp Iτ Iθ).
  - intros CD₁ CD₂ CD₃ F G₁ G₂ θ I₁ I₂ I₃ IF IG₁ IG₂ Iθ.
    exact (pre_whisker_twosided_disp_nat_trans_hor_comp IF Iθ).
  - intros CD₁ CD₂ CD₃ F G₁ G₂ τ I₁ I₂ I₃ IF₁ IF₂ IG Iτ.
    exact (post_whisker_twosided_disp_nat_trans_hor_comp IG Iτ).
Qed.

Definition disp_prebicat_data_twosided_disp_cat_hor_comp
  : disp_prebicat_data bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_twosided_disp_cat_hor_comp.
  - exact disp_prebicat_1_ops_twosided_disp_cat_hor_comp.
Defined.

Proposition disp_prebicat_laws_twosided_disp_cat_hor_comp
  : disp_prebicat_laws disp_prebicat_data_twosided_disp_cat_hor_comp.
Proof.
  repeat split ; intro ; intros ; apply isaprop_double_nat_trans_hor_comp.
Qed.

Definition disp_prebicat_twosided_disp_cat_hor_comp
  : disp_prebicat bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_twosided_disp_cat_hor_comp.
  - exact disp_prebicat_laws_twosided_disp_cat_hor_comp.
Defined.

Definition disp_bicat_twosided_disp_cat_hor_comp
  : disp_bicat bicat_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_twosided_disp_cat_hor_comp.
  - intro ; intros.
    apply isasetaprop.
    apply isaprop_double_nat_trans_hor_comp.
Defined.

Definition is_disp_invertible_2cell_hor_comp_over_id
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F : CD₁ --> CD₂}
           {Cm₁ : disp_bicat_twosided_disp_cat_hor_comp CD₁}
           {Cm₂ : disp_bicat_twosided_disp_cat_hor_comp CD₂}
           {FC GC : Cm₁ -->[ F ] Cm₂}
           (τ : FC ==>[ id2 _ ] GC)
  : is_disp_invertible_2cell
      (id2_invertible_2cell F)
      τ.
Proof.
  simple refine (_ ,, _ ,, _).
  - intros x y z h k ; cbn.
    pose (p := τ x y z h k) ; cbn in p.
    rewrite id_two_disp_right.
    rewrite id_two_disp_right in p.
    rewrite double_hor_comp_mor_id.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left.
    rewrite id_two_disp_left in p.
    rewrite transport_b_b_disp_mor2.
    rewrite transport_b_b_disp_mor2 in p.
    refine (_ @ !p @ _) ; use transportf_disp_mor2_eq ; apply idpath.
  - apply isaprop_double_nat_trans_hor_comp.
  - apply isaprop_double_nat_trans_hor_comp.
Qed.

Definition is_disp_invertible_2cell_hor_comp
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F G : CD₁ --> CD₂}
           {τ : invertible_2cell F G}
           {Cm₁ : disp_bicat_twosided_disp_cat_hor_comp CD₁}
           {Cm₂ : disp_bicat_twosided_disp_cat_hor_comp CD₂}
           {FC : Cm₁ -->[ F ] Cm₂}
           {GC : Cm₁ -->[ G ] Cm₂}
           (ττ : FC ==>[ τ ] GC)
  : is_disp_invertible_2cell τ ττ.
Proof.
  revert CD₁ CD₂ F G τ Cm₁ Cm₂ FC GC ττ.
  use J_2_1.
  - apply is_univalent_2_1_bicat_twosided_disp_cat.
  - cbn.
    intro ; intros.
    apply is_disp_invertible_2cell_hor_comp_over_id.
Qed.

Section HorCompDispInv2cell.
  Context {CD₁ CD₂ : bicat_twosided_disp_cat}
          {F : CD₁ --> CD₂}
          {Cm₁ : disp_bicat_twosided_disp_cat_hor_comp CD₁}
          {Cm₂ : disp_bicat_twosided_disp_cat_hor_comp CD₂}
          (FC GC : Cm₁ -->[ F ] Cm₂).

  Definition disp_bicat_twosided_disp_cat_hor_comp_weq_inv2cell
    : (∏ x y z h k, pr1 FC x y z h k = pr1 GC x y z h k)
      ≃
      disp_invertible_2cell (id2_invertible_2cell F) FC GC.
  Proof.
    use weqimplimpl.
    - intro p.
      simple refine (_ ,, _).
      + intros x y z h k ; cbn.
        rewrite id_two_disp_right.
        rewrite double_hor_comp_mor_id.
        rewrite id_two_disp_left.
        rewrite transport_b_b_disp_mor2.
        etrans.
        {
          apply maponpaths.
          exact (p x y z h k).
        }
        use transportf_disp_mor2_eq.
        apply idpath.
      + apply is_disp_invertible_2cell_hor_comp.
    - intros p x y z h k.
      pose (q := pr1 p x y z h k).
      cbn in q.
      rewrite id_two_disp_right in q.
      rewrite double_hor_comp_mor_id in q.
      rewrite id_two_disp_left in q.
      rewrite transport_b_b_disp_mor2 in q.
      refine (!_ @ maponpaths _ q @ transportfb_disp_mor2 _ _ _).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
    - repeat (use impred ; intro).
      apply isaset_disp_mor.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
      + intros.
        apply isaprop_double_nat_trans_hor_comp.
  Qed.
End HorCompDispInv2cell.

Definition disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2_1 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros CD₁ CD₂ F Cm₁ Cm₂ FC GC.
  use weqhomot.
  - refine (disp_bicat_twosided_disp_cat_hor_comp_weq_inv2cell FC GC
            ∘ weqonsecfibers
                _ _
                (λ x,
                 weqonsecfibers
                   _ _
                   (λ y,
                    weqonsecfibers
                      _ _
                      (λ z,
                       weqonsecfibers
                         _ _
                         (λ h, weqtoforallpaths _ _ _)
                       ∘ weqtoforallpaths _ _ _)
                    ∘ weqtoforallpaths _ _ _)
                 ∘ weqtoforallpaths _ _ _)
            ∘ weqtoforallpaths _ _ _
            ∘ path_sigma_hprop _ _ _ _)%weq.
    apply isaprop_double_functor_hor_comp_laws.
  - intro p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_disp_invertible_2cell.
    }
    apply isaprop_double_nat_trans_hor_comp.
Qed.

Section AdjEquivHorComp.
  Context {CD : bicat_twosided_disp_cat}
          (FF GG : disp_bicat_twosided_disp_cat_hor_comp CD)
          (τ : FF -->[ identity CD ] GG)
          (Hτ : ∏ (x y z : pr11 CD)
                  (h : pr12 CD x y)
                  (k : pr12 CD y z),
                is_iso_twosided_disp
                  (identity_is_z_iso _)
                  (identity_is_z_iso _)
                  (pr1 τ x y z h k)).

  Definition to_disp_left_adjequiv_hor_comp_inv_data
    : double_functor_hor_comp_data (twosided_disp_functor_identity _) GG FF
    := λ x y z h k, pr1 (Hτ x y z h k).

  Arguments to_disp_left_adjequiv_hor_id_inv_data /.

  Proposition to_disp_left_adjequiv_hor_comp_inv_laws
    : double_functor_hor_comp_laws to_disp_left_adjequiv_hor_comp_inv_data.
  Proof.
    intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn.
    pose (pr2 τ x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂) as p ; cbn in p.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply id_two_disp_right_alt.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 3 apply maponpaths.
      exact (inv_after_iso_twosided_disp_alt (Hτ _ _ _ _ _)).
    }
    rewrite !two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite assoc_two_disp.
      apply maponpaths.
      apply maponpaths_2.
      apply (pr2 τ).
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite !assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    apply transportf_disp_mor2_idpath.
  Qed.

  Definition to_disp_left_adjequiv_hor_comp_inv
    : double_functor_hor_comp (twosided_disp_functor_identity _) GG FF.
  Proof.
    use make_double_functor_hor_comp.
    - exact to_disp_left_adjequiv_hor_comp_inv_data.
    - exact to_disp_left_adjequiv_hor_comp_inv_laws.
  Defined.

  Proposition to_disp_left_adjequiv_hor_comp_unit
    : double_nat_trans_hor_comp
        (id_twosided_disp_nat_trans (twosided_disp_functor_identity _))
        (identity_hor_comp FF)
        (comp_hor_comp τ to_disp_left_adjequiv_hor_comp_inv).
  Proof.
    intros x y z h k ; cbn.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite double_hor_comp_mor_id.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    use transportf_disp_mor2_eq.
    apply idpath.
  Qed.

  Proposition to_disp_left_adjequiv_hor_comp_counit
    : double_nat_trans_hor_comp
        (id_twosided_disp_nat_trans (twosided_disp_functor_identity _))
        (comp_hor_comp to_disp_left_adjequiv_hor_comp_inv τ)
        (identity_hor_comp GG).
  Proof.
    intros x y z h k ; cbn.
    rewrite !id_two_disp_right.
    unfold transportb_disp_mor2.
    rewrite !transport_f_f_disp_mor2.
    rewrite double_hor_comp_mor_id.
    etrans.
    {
      apply maponpaths.
      apply Hτ.
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    use transportf_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition to_disp_left_adjequiv_hor_comp
    : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity CD) τ.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
    - exact to_disp_left_adjequiv_hor_comp_inv.
    - exact to_disp_left_adjequiv_hor_comp_unit.
    - exact to_disp_left_adjequiv_hor_comp_counit.
    - apply isaprop_double_nat_trans_hor_comp.
    - apply isaprop_double_nat_trans_hor_comp.
    - apply is_disp_invertible_2cell_hor_comp.
    - apply is_disp_invertible_2cell_hor_comp.
  Qed.
End AdjEquivHorComp.

Definition weq_disp_left_adjequiv_hor_comp_map
           {CD : bicat_twosided_disp_cat}
           {FF GG : disp_bicat_twosided_disp_cat_hor_comp CD}
           (τ : ∏ (x y z : pr11 CD)
                  (h : pr12 CD x y)
                  (k : pr12 CD y z),
                iso_twosided_disp
                  (identity_z_iso _) (identity_z_iso _)
                  (double_hor_comp (pr1 GG) h k)
                  (double_hor_comp (pr1 FF) h k))
           (Hτ : double_functor_hor_comp_laws
                   (FF := twosided_disp_functor_identity _)
                   (Cm₁ := FF) (Cm₂ := GG)
                   (λ x y z h k, pr1 (τ x y z h k)))
  : disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG.
Proof.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact τ.
    + exact Hτ.
  - use to_disp_left_adjequiv_hor_comp.
    intros x y z h k.
    exact (pr2 (τ x y z h k)).
Defined.

Definition disp_left_adjequiv_hor_comp_help
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           (F : adjoint_equivalence CD₁ CD₂)
           {Cm₁ : disp_bicat_twosided_disp_cat_hor_comp CD₁}
           {Cm₂ : disp_bicat_twosided_disp_cat_hor_comp CD₂}
           (τ : Cm₁ -->[ F ] Cm₂)
           (Hτ : ∏ (x y z : pr11 CD₁)
                   (h : pr12 CD₁ x y)
                   (k : pr12 CD₁ y z),
                 is_iso_twosided_disp
                   (identity_is_z_iso _)
                   (identity_is_z_iso _)
                   (pr1 τ x y z h k))
  : disp_left_adjoint_equivalence F τ.
Proof.
  revert CD₁ CD₂ F Cm₁ Cm₂ τ Hτ.
  use J_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat.
  - intros CD I₁ I₂ τ Hτ.
    use to_disp_left_adjequiv_hor_comp.
    exact Hτ.
Qed.

Definition disp_left_adjequiv_hor_comp
           {CD₁ CD₂ : bicat_twosided_disp_cat}
           {F : CD₁ --> CD₂}
           (HF : left_adjoint_equivalence F)
           {Cm₁ : disp_bicat_twosided_disp_cat_hor_comp CD₁}
           {Cm₂ : disp_bicat_twosided_disp_cat_hor_comp CD₂}
           (τ : Cm₁ -->[ F ] Cm₂)
           (Hτ : ∏ (x y z : pr11 CD₁)
                   (h : pr12 CD₁ x y)
                   (k : pr12 CD₁ y z),
                 is_iso_twosided_disp
                   (identity_is_z_iso _)
                   (identity_is_z_iso _)
                   (pr1 τ x y z h k))
  : disp_left_adjoint_equivalence HF τ.
Proof.
  exact (disp_left_adjequiv_hor_comp_help (F ,, HF) τ Hτ).
Qed.

Section FromAdjEquivHorComp.
  Context {CD : bicat_twosided_disp_cat}
          {FF GG : disp_bicat_twosided_disp_cat_hor_comp CD}
          (τ : disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG).

  Definition weq_disp_left_adjequiv_hor_comp_inv_iso
             {x y z : pr11 CD}
             (h : pr12 CD x y)
             (k : pr12 CD y z)
    : is_iso_twosided_disp (identity_is_z_iso x) (identity_is_z_iso z) (pr11 τ x y z h k).
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 (pr112 τ) x y z h k).
    - split.
      + abstract
          (cbn ;
           pose (p := pr2 (pr212 τ) x y z h k) ;
           cbn in p ;
           rewrite id_two_disp_right in p ;
           rewrite double_hor_comp_mor_id in p ;
           rewrite id_two_disp_left in p ;
           unfold transportb_disp_mor2 in p ;
           rewrite !transport_f_f_disp_mor2 in p ;
           refine (!(transportbf_disp_mor2 _ _ _) @ maponpaths _ p @ _) ;
           unfold transportb_disp_mor2 ;
           rewrite transport_f_f_disp_mor2 ;
           use transportf_disp_mor2_eq ;
           apply idpath).
      + abstract
          (pose (p := pr1 (pr212 τ) x y z h k) ;
           cbn in p ;
           rewrite id_two_disp_left in p ;
           rewrite double_hor_comp_mor_id in p ;
           rewrite id_two_disp_left in p ;
           unfold transportb_disp_mor2 in p ;
           rewrite !transport_f_f_disp_mor2 in p ;
           refine (!(transportbf_disp_mor2 _ _ _) @ maponpaths _ (!p) @ _) ;
           unfold transportb_disp_mor2 ;
           rewrite transport_f_f_disp_mor2 ;
           use transportf_disp_mor2_eq ;
           apply idpath).
Defined.

  Proposition weq_disp_left_adjequiv_hor_comp_inv_laws
    : double_functor_hor_comp_laws
        (FF := twosided_disp_functor_identity _)
        (Cm₁ := FF) (Cm₂ := GG)
        (λ x, pr11 τ x).
  Proof.
    intros x y f.
    exact (pr21 τ x y f).
  Qed.
End FromAdjEquivHorComp.

Definition weq_disp_left_adjequiv_hor_comp_inv
           {CD : bicat_twosided_disp_cat}
           {FF GG : disp_bicat_twosided_disp_cat_hor_comp CD}
           (τ : disp_adjoint_equivalence
                  (internal_adjoint_equivalence_identity CD)
                  FF GG)
  : ∑ (F : ∏ (x y z : pr11 CD)
             (h : pr12 CD x y)
             (k : pr12 CD y z),
           iso_twosided_disp
             (identity_z_iso _) (identity_z_iso _)
             (double_hor_comp (pr1 GG) h k)
             (double_hor_comp (pr1 FF) h k)),
    double_functor_hor_comp_laws
      (FF := twosided_disp_functor_identity _)
      (Cm₁ := FF) (Cm₂ := GG)
      (λ x y z h k, pr1 (F x y z h k)).
Proof.
  simple refine (_ ,, _).
  - intros x y z h k.
    simple refine (_ ,, _).
    + exact (pr11 τ x y z h k).
    + exact (weq_disp_left_adjequiv_hor_comp_inv_iso τ h k).
  - exact (weq_disp_left_adjequiv_hor_comp_inv_laws τ).
Defined.

Definition weq_disp_left_adjequiv_hor_comp
           {CD : bicat_twosided_disp_cat}
           (FF GG : disp_bicat_twosided_disp_cat_hor_comp CD)
  : (∑ (F : ∏ (x y z : pr11 CD)
              (h : pr12 CD x y)
              (k : pr12 CD y z),
            iso_twosided_disp
              (identity_z_iso _) (identity_z_iso _)
              (double_hor_comp (pr1 GG) h k)
              (double_hor_comp (pr1 FF) h k)),
     double_functor_hor_comp_laws
       (FF := twosided_disp_functor_identity _)
       (Cm₁ := FF) (Cm₂ := GG)
       (λ x y z h k, pr1 (F x y z h k)))
    ≃
    disp_adjoint_equivalence (internal_adjoint_equivalence_identity CD) FF GG.
Proof.
  use weq_iso.
  - intros F.
    exact (weq_disp_left_adjequiv_hor_comp_map (pr1 F) (pr2 F)).
  - exact weq_disp_left_adjequiv_hor_comp_inv.
  - abstract
      (intro τ ;
       use subtypePath ; [ intro ; apply isaprop_double_functor_hor_comp_laws | ] ;
       repeat (use funextsec ; intro) ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
       cbn ;
       apply idpath).
  - abstract
      (intro τ ;
       use subtypePath ;
       [ intro ;
         apply isaprop_disp_left_adjoint_equivalence ;
         [ apply is_univalent_2_1_bicat_twosided_disp_cat
         | apply disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp ]
       | ] ;
       use subtypePath ; [ intro ; apply isaprop_double_functor_hor_comp_laws | ] ;
       use funextsec ; intro ;
       cbn ;
       apply idpath).
Defined.

Definition disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2_0 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros CD FF GG.
  use weqhomot.
  - refine (weq_disp_left_adjequiv_hor_comp FF GG
            ∘ weqtotal2
                (weqonsecfibers
                   _ _
                   (λ x,
                    weqonsecfibers
                      _ _
                      (λ y,
                       weqonsecfibers
                         _ _
                         (λ z,
                          weqonsecfibers
                            _ _
                            (λ h,
                             weqonsecfibers
                               _ _
                               (λ k,
                                make_weq _ (pr22 CD _ _ _ _ (idpath _) (idpath _) _ _)
                                ∘ weqpathsinv0 _ _)
                             ∘ weqtoforallpaths _ _ _)
                          ∘ weqtoforallpaths _ _ _)
                       ∘ weqtoforallpaths _ _ _)
                    ∘ weqtoforallpaths _ _ _)
                 ∘ weqtoforallpaths _ _ _)
                _
            ∘ total2_paths_equiv _ _ _
            ∘ path_sigma_hprop _ _ _ (isaprop_hor_comp_laws _))%weq.
    cbn.
    induction FF as [ [ FF₁ FF₂ ] H ].
    induction GG as [ [ GG₁ GG₂ ] K ].
    intro p.
    pose (q := p : FF₁ = GG₁).
    assert (p = q) by apply idpath.
    induction q.
    rewrite X ; clear p X.
    cbn.
    use weqimplimpl.
    + intro q.
      intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn.
      rewrite q.
      rewrite id_two_disp_left.
      rewrite id_two_disp_right.
      rewrite transport_b_b_disp_mor2.
      use transportf_disp_mor2_eq.
      apply idpath.
    + intro q.
      use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y₁.
      use funextsec ; intro y₂.
      use funextsec ; intro z₁.
      use funextsec ; intro z₂.
      use funextsec ; intro v₁.
      use funextsec ; intro v₂.
      use funextsec ; intro v₃.
      use funextsec ; intro h₁.
      use funextsec ; intro h₂.
      use funextsec ; intro k₁.
      use funextsec ; intro k₂.
      use funextsec ; intro s₁.
      use funextsec ; intro s₂.
      pose (q x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ k₁ h₂ k₂ s₁ s₂) as p.
      cbn in p.
      rewrite id_two_disp_left in p.
      rewrite id_two_disp_right in p.
      rewrite transport_b_b_disp_mor2 in p.
      refine (!(transportfb_disp_mor2 _ _ _) @ maponpaths _ (!p) @ _).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
    + do 15 (use impred_isaset ; intro).
      apply isaset_disp_mor.
    + apply isaprop_double_functor_hor_comp_laws.
  - intro p.
    cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence.
      - apply is_univalent_2_1_bicat_twosided_disp_cat.
      - apply disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_double_functor_hor_comp_laws.
    }
    cbn.
    apply idpath.
Qed.

Definition disp_univalent_2_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_comp.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp.
Qed.

(** * 3. Two-sided displayed categories with identities and horizontal composition *)
Definition disp_bicat_twosided_disp_cat_id_hor_comp
  : disp_bicat bicat_twosided_disp_cat
  := disp_dirprod_bicat
       disp_bicat_twosided_disp_cat_hor_id
       disp_bicat_twosided_disp_cat_hor_comp.

Proposition disp_univalent_2_1_disp_bicat_twosided_disp_cat_id_hor_comp
  : disp_univalent_2_1 disp_bicat_twosided_disp_cat_id_hor_comp.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp.
Qed.

Proposition disp_univalent_2_0_disp_bicat_twosided_disp_cat_id_hor_comp
  : disp_univalent_2_0 disp_bicat_twosided_disp_cat_id_hor_comp.
Proof.
  use is_univalent_2_0_dirprod_bicat.
  - exact is_univalent_2_1_bicat_twosided_disp_cat.
  - exact disp_univalent_2_disp_bicat_twosided_disp_cat_hor_id.
  - exact disp_univalent_2_disp_bicat_twosided_disp_cat_hor_comp.
Qed.

Proposition disp_univalent_2_disp_bicat_twosided_disp_cat_id_hor_comp
  : disp_univalent_2 disp_bicat_twosided_disp_cat_id_hor_comp.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_id_hor_comp.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_id_hor_comp.
Qed.

Definition bicat_twosided_disp_cat_id_hor_comp
  : bicat
  := total_bicat disp_bicat_twosided_disp_cat_id_hor_comp.

Definition is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp
  : is_univalent_2_1 bicat_twosided_disp_cat_id_hor_comp.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_twosided_disp_cat.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_id_hor_comp.
Qed.

Definition is_univalent_2_0_bicat_twosided_disp_cat_id_hor_comp
  : is_univalent_2_0 bicat_twosided_disp_cat_id_hor_comp.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_id_hor_comp.
Qed.

Definition is_univalent_2_bicat_twosided_disp_cat_id_hor_comp
  : is_univalent_2 bicat_twosided_disp_cat_id_hor_comp.
Proof.
  split.
  - exact is_univalent_2_0_bicat_twosided_disp_cat_id_hor_comp.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
Qed.

(** * 4. Two-sided displayed categories with left unitors *)
Definition disp_cat_ob_mor_lunitor
  : disp_cat_ob_mor bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, double_cat_lunitor (pr12 CD) (pr22 CD)).
  - exact (λ CD₁ CD₂ l₁ l₂ FF, double_functor_lunitor l₁ l₂ (pr12 FF) (pr22 FF)).
Defined.

Definition disp_cat_id_comp_lunitor
  : disp_cat_id_comp
      bicat_twosided_disp_cat_id_hor_comp
      disp_cat_ob_mor_lunitor.
Proof.
  split.
  - intros CD l.
    exact (identity_functor_lunitor l).
  - intros CD₁ CD₂ CD₃ FF GG l₁ l₂ l₃ FFl GGl.
    exact (comp_functor_lunitor FFl GGl).
Qed.

Definition disp_cat_data_lunitor
  : disp_cat_data bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_lunitor.
  - exact disp_cat_id_comp_lunitor.
Defined.

Definition disp_bicat_lunitor
  : disp_bicat bicat_twosided_disp_cat_id_hor_comp
  := disp_cell_unit_bicat disp_cat_data_lunitor.

Definition disp_univalent_2_1_disp_bicat_lunitor
  : disp_univalent_2_1 disp_bicat_lunitor.
Proof.
  use disp_cell_unit_bicat_univalent_2_1.
  intros.
  apply isaprop_double_functor_lunitor.
Qed.

Definition disp_univalent_2_0_disp_bicat_lunitor
  : disp_univalent_2_0 disp_bicat_lunitor.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
  - intros.
    apply isaprop_double_functor_lunitor.
  - intros.
    apply isaset_double_cat_lunitor.
  - intros CD FF GG H.
    induction H as [ H₁ H₂ ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_lunitor_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    pose (p := H₁ x y f).
    pose (q := H₂ x y f).
    cbn in p, q.
    rewrite id_two_disp_right in p.
    rewrite two_disp_pre_whisker_b in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    refine (_ @ !p).
    refine (!_).
    apply transportf_disp_mor2_idpath.
Qed.

Definition disp_univalent_2_disp_bicat_lunitor
  : disp_univalent_2 disp_bicat_lunitor.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_lunitor.
  - exact disp_univalent_2_1_disp_bicat_lunitor.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_lunitor_help
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           (F : adjoint_equivalence C₁ C₂)
           {l₁ : disp_bicat_lunitor C₁}
           {l₂ : disp_bicat_lunitor C₂}
           (Fl : l₁ -->[ F ] l₂)
  : disp_left_adjoint_equivalence F Fl.
Proof.
  revert C₁ C₂ F l₁ l₂ Fl.
  use J_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat_id_hor_comp.
  - intros C l₁ l₂ Fl.
    use disp_cell_unit_bicat_left_adjoint_equivalence.
    intros x y f ; cbn.
    pose (p := Fl x y f) ; cbn in p.
    rewrite double_hor_comp_mor_id.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite two_disp_pre_whisker_f in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite p.
    rewrite transport_f_f_disp_mor2.
    refine (!_).
    apply transportf_disp_mor2_idpath.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_lunitor
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           {F : C₁ --> C₂}
           (HF : left_adjoint_equivalence F)
           {l₁ : disp_bicat_lunitor C₁}
           {l₂ : disp_bicat_lunitor C₂}
           (Fl : l₁ -->[ F ] l₂)
  : disp_left_adjoint_equivalence HF Fl.
Proof.
  exact (is_disp_left_adjoint_equivalence_disp_bicat_lunitor_help (F ,, HF) Fl).
Qed.

(** * 5. Two-sided displayed categories with right unitors *)
Definition disp_cat_ob_mor_runitor
  : disp_cat_ob_mor bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, double_cat_runitor (pr12 CD) (pr22 CD)).
  - exact (λ CD₁ CD₂ l₁ l₂ FF, double_functor_runitor l₁ l₂ (pr12 FF) (pr22 FF)).
Defined.

Definition disp_cat_id_comp_runitor
  : disp_cat_id_comp
      bicat_twosided_disp_cat_id_hor_comp
      disp_cat_ob_mor_runitor.
Proof.
  split.
  - intros CD l.
    exact (identity_functor_runitor l).
  - intros CD₁ CD₂ CD₃ FF GG l₁ l₂ l₃ FFl GGl.
    exact (comp_functor_runitor FFl GGl).
Qed.

Definition disp_cat_data_runitor
  : disp_cat_data bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_runitor.
  - exact disp_cat_id_comp_runitor.
Defined.

Definition disp_bicat_runitor
  : disp_bicat bicat_twosided_disp_cat_id_hor_comp
  := disp_cell_unit_bicat disp_cat_data_runitor.

Definition disp_univalent_2_1_disp_bicat_runitor
  : disp_univalent_2_1 disp_bicat_runitor.
Proof.
  use disp_cell_unit_bicat_univalent_2_1.
  intros.
  apply isaprop_double_functor_runitor.
Qed.

Definition disp_univalent_2_0_disp_bicat_runitor
  : disp_univalent_2_0 disp_bicat_runitor.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
  - intros.
    apply isaprop_double_functor_runitor.
  - intros.
    apply isaset_double_cat_runitor.
  - intros CD FF GG H.
    induction H as [ H₁ H₂ ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_runitor_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    pose (p := H₁ x y f).
    pose (q := H₂ x y f).
    cbn in p, q.
    rewrite id_two_disp_right in p.
    rewrite two_disp_pre_whisker_b in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    refine (_ @ !p).
    refine (!_).
    apply transportf_disp_mor2_idpath.
Qed.

Definition disp_univalent_2_disp_bicat_runitor
  : disp_univalent_2 disp_bicat_runitor.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_runitor.
  - exact disp_univalent_2_1_disp_bicat_runitor.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_runitor_help
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           (F : adjoint_equivalence C₁ C₂)
           {r₁ : disp_bicat_runitor C₁}
           {r₂ : disp_bicat_runitor C₂}
           (Fr : r₁ -->[ F ] r₂)
  : disp_left_adjoint_equivalence F Fr.
Proof.
  revert C₁ C₂ F r₁ r₂ Fr.
  use J_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat_id_hor_comp.
  - intros C r₁ r₂ Fr.
    use disp_cell_unit_bicat_left_adjoint_equivalence.
    intros x y f ; cbn.
    pose (p := Fr x y f) ; cbn in p.
    rewrite double_hor_comp_mor_id.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite two_disp_pre_whisker_f in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite p.
    rewrite transport_f_f_disp_mor2.
    refine (!_).
    apply transportf_disp_mor2_idpath.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_runitor
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           {F : C₁ --> C₂}
           (HF : left_adjoint_equivalence F)
           {r₁ : disp_bicat_runitor C₁}
           {r₂ : disp_bicat_runitor C₂}
           (Fr : r₁ -->[ F ] r₂)
  : disp_left_adjoint_equivalence HF Fr.
Proof.
  exact (is_disp_left_adjoint_equivalence_disp_bicat_runitor_help (F ,, HF) Fr).
Qed.

(** * 6. Two-sided displayed categories with associators *)
Definition disp_cat_ob_mor_lassociator
  : disp_cat_ob_mor bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, double_cat_associator (pr22 CD)).
  - exact (λ CD₁ CD₂ a₁ a₂ FF, double_functor_associator a₁ a₂ (pr22 FF)).
Defined.

Definition disp_cat_id_comp_lassociator
  : disp_cat_id_comp
      bicat_twosided_disp_cat_id_hor_comp
      disp_cat_ob_mor_lassociator.
Proof.
  split.
  - intros.
    apply identity_functor_associator.
  - intros CD₁ CD₂ CD₃ FF GG a₁ a₂ a₃ FFa GGa.
    exact (comp_functor_associator FFa GGa).
Qed.

Definition disp_cat_data_lassociator
  : disp_cat_data bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_lassociator.
  - exact disp_cat_id_comp_lassociator.
Defined.

Definition disp_bicat_lassociator
  : disp_bicat bicat_twosided_disp_cat_id_hor_comp
  := disp_cell_unit_bicat disp_cat_data_lassociator.

Definition disp_univalent_2_1_disp_bicat_lassociator
  : disp_univalent_2_1 disp_bicat_lassociator.
Proof.
  use disp_cell_unit_bicat_univalent_2_1.
  intros.
  apply isaprop_double_functor_associator.
Qed.

Definition disp_univalent_2_0_disp_bicat_lassociator
  : disp_univalent_2_0 disp_bicat_lassociator.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
  - intros.
    apply isaprop_double_functor_associator.
  - intros.
    apply isaset_double_cat_associator.
  - intros CD FF GG H.
    induction H as [ H₁ H₂ ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_associator_laws.
    }
    use funextsec ; intro w.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro z.
    use funextsec ; intro f.
    use funextsec ; intro g.
    use funextsec ; intro h.
    pose (p := H₁ w x y z f g h).
    cbn in p.
    rewrite id_two_disp_right in p.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_right in p.
    rewrite transport_b_b_disp_mor2 in p.
    rewrite double_hor_comp_mor_id in p.
    rewrite id_two_disp_left in p.
    rewrite two_disp_pre_whisker_b in p.
    rewrite id_two_disp_left in p.
    rewrite transport_b_b_disp_mor2 in p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    refine (_ @ maponpaths _ (!p) @ transportfb_disp_mor2 _ _ _).
    refine (!_).
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply transportf_disp_mor2_idpath.
Qed.

Definition disp_univalent_2_disp_bicat_lassociator
  : disp_univalent_2 disp_bicat_lassociator.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_lassociator.
  - exact disp_univalent_2_1_disp_bicat_lassociator.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_lassociator_help
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           (F : adjoint_equivalence C₁ C₂)
           {a₁ : disp_bicat_lassociator C₁}
           {a₂ : disp_bicat_lassociator C₂}
           (Fa : a₁ -->[ F ] a₂)
  : disp_left_adjoint_equivalence F Fa.
Proof.
  revert C₁ C₂ F a₁ a₂ Fa.
  use J_2_0.
  - exact is_univalent_2_0_bicat_twosided_disp_cat_id_hor_comp.
  - intros C a₁ a₂ Fa.
    use disp_cell_unit_bicat_left_adjoint_equivalence.
    intros w x y z f g h ; cbn.
    pose (p := Fa w x y z f g h) ; cbn in p.
    rewrite !double_hor_comp_mor_id.
    rewrite !double_hor_comp_mor_id in p.
    rewrite id_two_disp_right.
    rewrite id_two_disp_right.
    rewrite id_two_disp_right.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite id_two_disp_right in p.
    rewrite id_two_disp_right in p.
    rewrite id_two_disp_right in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    rewrite two_disp_pre_whisker_f.
    rewrite id_two_disp_left.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite two_disp_pre_whisker_f in p.
    rewrite id_two_disp_left in p.
    unfold transportb_disp_mor2 in p.
    rewrite transport_f_f_disp_mor2 in p.
    refine (_ @ !p @ _).
    + use transportf_disp_mor2_eq.
      apply idpath.
    + use transportf_disp_mor2_eq.
      apply idpath.
Qed.

Definition is_disp_left_adjoint_equivalence_disp_bicat_lassociator
           {C₁ C₂ : bicat_twosided_disp_cat_id_hor_comp}
           {F : C₁ --> C₂}
           (HF : left_adjoint_equivalence F)
           {a₁ : disp_bicat_lassociator C₁}
           {a₂ : disp_bicat_lassociator C₂}
           (Fa : a₁ -->[ F ] a₂)
  : disp_left_adjoint_equivalence HF Fa.
Proof.
  exact (is_disp_left_adjoint_equivalence_disp_bicat_lassociator_help (F ,, HF) Fa).
Qed.

(** * 7. Two-sided displayed categories with unitors and associators *)
Definition disp_bicat_unitors_and_associator
  : disp_bicat bicat_twosided_disp_cat_id_hor_comp
  := disp_dirprod_bicat
       disp_bicat_lunitor
       (disp_dirprod_bicat
          disp_bicat_runitor
          disp_bicat_lassociator).

Proposition disp_univalent_2_disp_bicat_unitors_and_associator
  : disp_univalent_2 disp_bicat_unitors_and_associator.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
  - exact disp_univalent_2_disp_bicat_lunitor.
  - use is_univalent_2_dirprod_bicat.
    + exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
    + exact disp_univalent_2_disp_bicat_runitor.
    + exact disp_univalent_2_disp_bicat_lassociator.
Qed.

Definition bicat_unitors_and_associator
  : bicat
  := total_bicat disp_bicat_unitors_and_associator.

Definition is_univalent_2_bicat_unitors_and_associator
  : is_univalent_2 bicat_unitors_and_associator.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_unitors_and_associator.
  - exact is_univalent_2_bicat_twosided_disp_cat_id_hor_comp.
Qed.

Definition is_univalent_2_1_bicat_unitors_and_associator
  : is_univalent_2_1 bicat_unitors_and_associator.
Proof.
  exact (pr2 is_univalent_2_bicat_unitors_and_associator).
Qed.

Definition is_univalent_2_0_bicat_unitors_and_associator
  : is_univalent_2_0 bicat_unitors_and_associator.
Proof.
  exact (pr1 is_univalent_2_bicat_unitors_and_associator).
Qed.

(** * 8. Displayed bicategory of double categories *)
Definition bicat_of_double_cats
  : bicat
  := fullsubbicat bicat_unitors_and_associator
       (λ CD,
        let l := pr12 CD in
        let r := pr122 CD in
        let a := pr222 CD in
        triangle_law l r a × pentagon_law a).

Definition is_univalent_2_bicat_of_double_cats
  : is_univalent_2 bicat_of_double_cats.
Proof.
  use is_univalent_2_fullsubbicat.
  - exact is_univalent_2_bicat_unitors_and_associator.
  - intros L.
    apply isapropdirprod.
    + apply isaprop_triangle_law.
    + apply isaprop_pentagon_law.
Qed.
