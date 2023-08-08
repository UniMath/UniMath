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
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DoubleCategory.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DoubleFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DoubleTransformation.
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

Local Open Scope cat.

(**
 1. Two-sided displayed categories with identities
 *)
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

Definition disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2_1 disp_bicat_twosided_disp_cat_hor_id.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros x y f xx yy ff gg ; cbn.
Admitted.

Definition disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2_0 disp_bicat_twosided_disp_cat_hor_id.
Proof.
Admitted.

Definition disp_univalent_2_disp_bicat_twosided_disp_cat_hor_id
  : disp_univalent_2 disp_bicat_twosided_disp_cat_hor_id.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_id.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_id.
Qed.

(**
 2. Two-sided displayed categories with horizontal composition
 *)
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

Definition disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2_1 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
Admitted.

Definition disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2_0 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
Admitted.

Definition disp_univalent_2_disp_bicat_twosided_disp_cat_hor_comp
  : disp_univalent_2 disp_bicat_twosided_disp_cat_hor_comp.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_twosided_disp_cat_hor_comp.
  - exact disp_univalent_2_1_disp_bicat_twosided_disp_cat_hor_comp.
Qed.

(**
 3. Two-sided displayed categories with identities and horizontal composition
 *)
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

(**
 4. Two-sided displayed categories with left unitors
 *)
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
    unfold transportb in p.
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

(**
 5. Two-sided displayed categories with right unitors
 *)
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
    unfold transportb in p.
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

(**
 6. Two-sided displayed categories with associators
 *)
Definition disp_cat_ob_mor_lassociator
  : disp_cat_ob_mor bicat_twosided_disp_cat_id_hor_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, double_cat_associator (pr22 CD)).
  - admit.
    (*exact (λ CD₁ CD₂ a₁ a₂ FF, double_functor_associator a₁ a₂ (pr22 FF)).*)
Admitted.

Definition disp_cat_id_comp_lassociator
  : disp_cat_id_comp
      bicat_twosided_disp_cat_id_hor_comp
      disp_cat_ob_mor_lassociator.
Proof.
  split.
  - admit.
  - admit.
Admitted.

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
Admitted.

Definition disp_univalent_2_0_disp_bicat_lassociator
  : disp_univalent_2_0 disp_bicat_lassociator.
Proof.
  use disp_cell_unit_bicat_univalent_2_0.
  - exact is_univalent_2_1_bicat_twosided_disp_cat_id_hor_comp.
  - intros.
    admit.
  - intros.
    admit.
  -
Admitted.

Definition disp_univalent_2_disp_bicat_lassociator
  : disp_univalent_2 disp_bicat_lassociator.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_lassociator.
  - exact disp_univalent_2_1_disp_bicat_lassociator.
Qed.

(**
 7. Two-sided displayed categories with unitors and associators
 *)
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

(**
 8. Displayed bicategory of double categories
 *)
Definition bicat_of_double_cats
  : bicat.
Proof.
  refine (fullsubbicat bicat_unitors_and_associator _).
Admitted.

Definition is_univalent_2_bicat_of_double_cats
  : is_univalent_2 bicat_of_double_cats.
Proof.
  (* use is_univalent_2_fullsubbicat. *)
Admitted.
