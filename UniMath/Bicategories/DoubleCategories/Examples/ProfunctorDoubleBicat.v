(*****************************************************************************************

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.categories.HSET.SetCoends.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Squares.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ProfunctorTwosidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.

Local Open Scope cat.

Local Notation "∁" := (op2_bicat bicat_of_univ_cats).

Definition TODO { A : UU } : A.
Admitted.

Definition univalent_profunctor_twosided_disp_cat_ob_mor
  : twosided_disp_cat_ob_mor ∁ ∁.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C₁ C₂ : univalent_category), C₁ ↛ C₂).
  - exact (λ (C₁ C₂ D₁ D₂ : univalent_category)
             (P : C₁ ↛ D₁)
             (Q : C₂ ↛ D₂)
             (F : C₁ ⟶ C₂)
             (G : D₁ ⟶ D₂),
           profunctor_square G F P Q).
Defined.

Proposition univalent_twosided_disp_cat_id_comp
  : twosided_disp_cat_id_comp univalent_profunctor_twosided_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ C D P, id_h_profunctor_square P).
  - exact (λ C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ F₁ F₂ G₁ G₂ τ₁ τ₂, comp_h_profunctor_square τ₁ τ₂).
Defined.

Definition univalent_profunctor_twosided_disp_cat_data
  : twosided_disp_cat_data ∁ ∁.
Proof.
  simple refine (_ ,, _).
  - exact univalent_profunctor_twosided_disp_cat_ob_mor.
  - exact univalent_twosided_disp_cat_id_comp.
Defined.

Definition univalent_profunctor_ver_sq_bicat
  : ver_sq_bicat.
Proof.
  use make_ver_sq_bicat.
  - exact ∁.
  - exact univalent_profunctor_twosided_disp_cat_data.
Defined.

Definition univalent_profunctor_ver_sq_bicat_ver_id_comp
  : ver_sq_bicat_ver_id_comp univalent_profunctor_ver_sq_bicat.
Proof.
  split.
  - split.
    + exact (λ (C : univalent_category), id_profunctor C).
    + exact (λ (C₁ C₂ C₃ : univalent_category)
               (P : C₁ ↛ C₂)
               (Q : C₂ ↛ C₃),
             comp_profunctor P Q).
  - exact (λ (C₁ C₂ : univalent_category) (P Q : C₁ ↛ C₂), profunctor_nat_trans P Q).
Defined.

Definition univalent_profunctor_ver_sq_bicat_id_comp_cells
  : ver_sq_bicat_id_comp_cells univalent_profunctor_ver_sq_bicat_ver_id_comp.
Proof.
  repeat split.
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           profunctor_nat_trans_id P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           lunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           runitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           linvunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ : univalent_category)
             (P : C₁ ↛ C₂),
           rinvunitor_profunctor_nat_trans P).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (P : C₁ ↛ C₂)
             (Q : C₂ ↛ C₃)
             (R : C₃ ↛ C₄),
           inv_associator_profunctor_nat_trans P Q R).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (P : C₁ ↛ C₂)
             (Q : C₂ ↛ C₃)
             (R : C₃ ↛ C₄),
           associator_profunctor_nat_trans P Q R).
  - exact (λ (C₁ C₂ : univalent_category)
             (P Q R : C₁ ↛ C₂)
             (τ : profunctor_nat_trans P Q)
             (θ : profunctor_nat_trans Q R),
           profunctor_nat_trans_comp τ θ).
  - apply TODO. (* whisker *)
  - apply TODO. (* whisker *)
Defined.

Proposition univalent_profunctor_ver_sq_bicat_prebicat_laws
  : ver_sq_bicat_prebicat_laws univalent_profunctor_ver_sq_bicat_id_comp_cells.
Proof.
  repeat split.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ C₃ P Q₁ Q₂ Q₃ τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ C₃ P₁ P₂ P₃ Q τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ P Q τ.
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    admit.
  - intros C₁ C₂ C₃ C₄ P Q R₁ R₂ τ.
    use eq_profunctor_nat_trans.
    intros z w h ; cbn.
    admit.
  - intros C₁ C₂ C₃ C₄ P Q₁ Q₂ R τ.
    use eq_profunctor_nat_trans.
    intros z w h ; cbn.
    admit.
  - intros C₁ C₂ C₃ C₄ P₁ P₂ Q R τ.
    use eq_profunctor_nat_trans.
    intros z w h ; cbn.
    admit.
  - intros C₁ C₂ C₃ P₁ P₂ Q₁ Q₂ τ₁ τ₂.
    use eq_profunctor_nat_trans.
    intros z x h ; cbn.
    admit.
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_runitor_profunctor_nat_trans P)).
  - intros C₁ C₂ P.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_runitor_profunctor_nat_trans P)).
  - intros C₁ C₂ C₃ C₄ P Q R.
    exact (inv_profunctor_nat_trans_right
             (is_profunctor_nat_iso_associator_profunctor_nat_trans P Q R)).
  - intros C₁ C₂ C₃ C₄ P Q R.
    exact (inv_profunctor_nat_trans_left
             (is_profunctor_nat_iso_associator_profunctor_nat_trans P Q R)).
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_nat_trans.
    intros z x h ; cbn.
    admit.
  - intros C₁ C₂ C₃ C₄ C₅ P₁ P₂ P₃ P₄.
    use eq_profunctor_nat_trans.
    intros z v h ; cbn.
    admit.
Admitted.

Definition univalent_profunctor_ver_bicat_sq_bicat
  : ver_bicat_sq_bicat.
Proof.
  use make_ver_bicat_sq_bicat.
  - exact univalent_profunctor_ver_sq_bicat.
  - exact univalent_profunctor_ver_sq_bicat_ver_id_comp.
  - exact univalent_profunctor_ver_sq_bicat_id_comp_cells.
  - exact univalent_profunctor_ver_sq_bicat_prebicat_laws.
  - abstract
      (intros C₁ C₂ P Q ;
       apply isaset_profunctor_nat_trans).
Defined.

Definition univalent_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq
  : ver_bicat_sq_bicat_ver_id_comp_sq univalent_profunctor_ver_bicat_sq_bicat.
Proof.
  split.
  - exact (λ (C₁ C₂ : univalent_category)
             (F : C₁ ⟶ C₂),
           id_v_profunctor_square F).
  - exact (λ (C₁ C₂ C₃ D₁ D₂ D₃ : univalent_category)
             (F₁ : C₁ ⟶ D₁)
             (F₂ : C₂ ⟶ D₂)
             (F₃ : C₃ ⟶ D₃)
             (P₁ : C₁ ↛ C₂)
             (P₂ : C₂ ↛ C₃)
             (Q₁ : D₁ ↛ D₂)
             (Q₂ : D₂ ↛ D₃)
             (τ : profunctor_square F₂ F₁ P₁ Q₁)
             (θ : profunctor_square F₃ F₂ P₂ Q₂),
           comp_v_profunctor_square τ θ).
Defined.

Definition univalent_profunctor_ver_bicat_sq_bicat_ver_id_comp
  : ver_bicat_sq_bicat_ver_id_comp.
Proof.
  use make_ver_bicat_sq_bicat_ver_id_comp.
  - exact univalent_profunctor_ver_bicat_sq_bicat.
  - exact univalent_profunctor_ver_bicat_sq_bicat_ver_id_comp_sq.
Defined.

Definition univalent_profunctor_double_bicat_whiskering
  : double_bicat_whiskering univalent_profunctor_ver_bicat_sq_bicat_ver_id_comp.
Proof.
  repeat split.
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P₁ P₂ : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : profunctor_nat_trans P₁ P₂)
             (s : profunctor_square G F P₂ Q),
           lwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q₁ Q₂ : C₂ ↛ C₄)
             (τ : profunctor_nat_trans Q₁ Q₂)
             (s : profunctor_square G F P Q₁),
           rwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F₁ F₂ : C₁ ⟶ C₂)
             (G : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : F₂ ⟹ F₁)
             (s : profunctor_square G F₂ P Q),
           dwhisker_profunctor_square τ s).
  - exact (λ (C₁ C₂ C₃ C₄ : univalent_category)
             (F : C₁ ⟶ C₂)
             (G₁ G₂ : C₃ ⟶ C₄)
             (P : C₁ ↛ C₃)
             (Q : C₂ ↛ C₄)
             (τ : G₂ ⟹ G₁)
             (s : profunctor_square G₁ F P Q),
           uwhisker_profunctor_square τ s).
Defined.

Definition univalent_profunctor_ver_bicat_sq_id_comp_whisker
  : ver_bicat_sq_id_comp_whisker.
Proof.
  use make_ver_bicat_sq_id_comp_whisker.
  - exact univalent_profunctor_ver_bicat_sq_bicat_ver_id_comp.
  - exact univalent_profunctor_double_bicat_whiskering.
Defined.

Proposition univalent_profunctor_whisker_square_bicat_law
  : whisker_square_bicat_law univalent_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P₁ P₂ P₃ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q₁ Q₂ Q₃ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ G P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_comp.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite lmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ G₃ P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite lmap_comp.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G₁ G₂ P Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite rmap_lmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G P₁ P₂ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G P Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite profunctor_nat_trans_rmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ P₁ P₂ Q τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ P Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite profunctor_nat_trans_lmap.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P₁ P₂ Q₁ Q₂ τ₁ τ₂ θ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ P Q τ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    rewrite id_left, id_right.
    rewrite nat_trans_ax.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq ; clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm θ₁ θ₂ z x y h h').
    }
    rewrite comp_profunctor_mor_comm.
    rewrite lmap_id.
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (dwhisker_profunctor_square τ θ₁) θ₂
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F G H₁ H₂ P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm θ₁ θ₂ z x y h h').
    }
    rewrite comp_profunctor_mor_comm.
    rewrite rmap_id.
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ (uwhisker_profunctor_square τ θ₂)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F G₁ G₂ H P₁ P₂ Q₁ Q₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    use mor_from_comp_profunctor_ob_eq ; cbn.
    clear h.
    intros y h h'.
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ (dwhisker_profunctor_square τ θ₂)
               z x y
               h h').
    }
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (uwhisker_profunctor_square τ θ₁) θ₂
               z x y h h').
    }
    cbn.
    rewrite comp_profunctor_ob_in_comm.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P₁ P₂ Q R τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q₁ Q₂ R τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ F₁ F₂ G₁ G₂ P Q R₁ R₂ τ θ₁ θ₂ ; cbn in *.
    use eq_profunctor_square ; intros z x h ; cbn.
    apply idpath.
Qed.

Proposition univalent_profunctor_double_bicat_id_comp_square_laws
  : double_bicat_id_comp_square_laws univalent_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₀ P₁ P₂ Q₁ Q₂ R₁ R₂ F₁ F₂ G₁ G₂ H₁ H₂ τ₁ τ₂ θ₁ θ₂.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h ; cbn in *.
    intros y h h'.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₁ τ₂ z x y h h').
    }
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               θ₁ θ₂
               (H₁ z) (F₁ x) (G₁ y)
               (τ₁ y x h) (τ₂ z y h')).
    }
    refine (!_).
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (comp_h_profunctor_square τ₁ θ₁) (comp_h_profunctor_square τ₂ θ₂)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intro C.
    use eq_profunctor_square ; intros y x h ; cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_square ; intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn in *.
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (id_h_profunctor_square P) (id_h_profunctor_square Q)
               z x y
               h h').
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ P Q.
    use eq_profunctor_square ; intros z x h ; cbn in *.
    apply idpath.
Qed.

Proposition univalent_profunctor_double_bicat_cylinder_laws
  : double_bicat_cylinder_laws univalent_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  repeat split.
  - intros C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ F₁ F₂ F₃ G₁ G₂ G₃ P₁ P₂ P₃ P₄ τ₁ τ₂ τ₃.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ F₁ F₂ F₃ F₄ P₁ P₂ P₃ Q₁ Q₂ Q₃ τ₁ τ₂ τ₃.
    use eq_profunctor_square.
    intros x₁ x₂ h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros x₃ h h'.
    cbn in *.
    use (mor_from_comp_profunctor_ob_eq
           P₂ P₃
           x₁ x₃
           (λ h',
            comp_v_profunctor_square_mor
              (comp_v_profunctor_square τ₁ τ₂) τ₃
              x₁ x₂
              (associator_profunctor_nat_trans_mor
                 P₁ P₂ P₃ x₁ x₂
                 (comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x₃ h h')))
           (λ h',
            associator_profunctor_nat_trans_mor
              Q₁ Q₂ Q₃ (F₄ x₁) (F₁ x₂)
              (comp_v_profunctor_square_mor
                 τ₁ (comp_v_profunctor_square τ₂ τ₃) x₁ x₂
                 (comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x₃ h h')))).
    clear h'.
    intros x₄ h' h'' ; cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply associator_profunctor_nat_trans_mor_ob_comm.
    }
    etrans.
    {
      exact (comp_v_profunctor_square_mor_comm
               (comp_v_profunctor_square τ₁ τ₂) τ₃
               _ _ _
               _ _).
    }
    cbn.
    etrans.
    {
      apply maponpaths_2.
      exact (comp_v_profunctor_square_mor_comm τ₁ τ₂ _ _ _ _ _).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₁ (comp_v_profunctor_square τ₂ τ₃) _ _ _ _ _).
    }
    rewrite associator_profunctor_nat_trans_mor_comm ; cbn.
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ₂ τ₃ _ _ _ _ _).
    }
    etrans.
    {
      exact (associator_profunctor_nat_trans_mor_ob_comm
               Q₁ Q₂ Q₃
               (τ₁ x₃ x₂ h)
               (τ₂ x₄ x₃ h')
               (τ₃ x₁ x₄ h'')).
    }
    cbn.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros z h h' ; cbn in *.
    rewrite lunitor_profunctor_nat_trans_mor_comm.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm (id_v_profunctor_square F) τ y x z h h').
    }
    cbn.
    rewrite lunitor_profunctor_nat_trans_mor_comm.
    rewrite (profunctor_square_rmap τ).
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    rewrite lmap_id, rmap_id.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G P Q τ.
    use eq_profunctor_square.
    intros y x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros z h h' ; cbn in *.
    rewrite runitor_profunctor_nat_trans_mor_comm.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (comp_v_profunctor_square_mor_comm τ (id_v_profunctor_square G) y x z h h').
    }
    cbn.
    rewrite runitor_profunctor_nat_trans_mor_comm.
    rewrite (profunctor_square_lmap τ).
    apply idpath.
  - admit.
  - admit.
Admitted.

Proposition univalent_profunctor_double_bicat_laws
  : double_bicat_laws univalent_profunctor_ver_bicat_sq_id_comp_whisker.
Proof.
  use make_double_bicat_laws.
  - exact univalent_profunctor_whisker_square_bicat_law.
  - exact univalent_profunctor_double_bicat_id_comp_square_laws.
  - exact univalent_profunctor_double_bicat_cylinder_laws.
  - intro ; intros.
    apply isaset_profunctor_square.
Qed.

Definition univalent_profunctor_verity_double_bicat
  : verity_double_bicat.
Proof.
  use make_verity_double_bicat.
  - exact univalent_profunctor_ver_bicat_sq_id_comp_whisker.
  - exact univalent_profunctor_double_bicat_laws.
Defined.
