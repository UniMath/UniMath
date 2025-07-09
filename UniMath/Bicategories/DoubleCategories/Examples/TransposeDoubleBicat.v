(*****************************************************************************************

 The transpose of Verity double bicategories

 The notion of Verity double bicategory is symmetric, because it is weak in both
 directions. For that reason, every Verity double bicategory has a transpose, which is
 the Verity double bicategory obtained by swapping the vertical and horizontal morphisms.

 Contents
 1. The 2-sided displayed category of the transpose
 2. The vertical bicategory of the transpose
 3. The whiskering operations
 4. The transpose of a Verity double bicategory

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.

Local Open Scope cat.
Local Open Scope double_bicat.

Section Transpose.
  Context (B : verity_double_bicat).

  Let 𝕍 : bicat := ver_bicat_of_verity_double_bicat B. (* \bV *)
  Let ℍ : bicat := hor_bicat_of_verity_double_bicat B. (* \bH *)

  (** * 1. The 2-sided displayed category of the transpose *)
  Definition transpose_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor 𝕍 𝕍.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x y : B), x --> y).
    - exact (λ (x₁ x₂ y₁ y₂ : B)
               (h₁ : x₁ --> y₁) (h₂ : x₂ --> y₂)
               (v₁ : x₁ -|-> x₂) (v₂ : y₁ -|-> y₂),
             square_double_bicat h₁ h₂ v₁ v₂).
  Defined.

  Definition transpose_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp transpose_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x y : B) (h : x --> y), id_v_square_bicat h).
    - exact (λ (x₁ y₁ z₁ x₂ y₂ z₂ : B)
               (hx : x₁ --> x₂)
               (hy : y₁ --> y₂)
               (hz : z₁ --> z₂)
               (v₁ : x₁ -|-> y₁) (v₂ : y₁ -|-> z₁)
               (w₁ : x₂ -|-> y₂) (w₂ : y₂ -|-> z₂)
               (s₁ : square_double_bicat hx hy v₁ w₁)
               (s₂ : square_double_bicat hy hz v₂ w₂),
             s₁ ⋆v s₂).
  Defined.

  Definition transpose_twosided_disp_cat_data
    : twosided_disp_cat_data 𝕍 𝕍.
  Proof.
    simple refine (_ ,, _).
    - exact transpose_twosided_disp_cat_ob_mor.
    - exact transpose_twosided_disp_cat_id_comp.
  Defined.

  Definition transpose_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact 𝕍.
    - exact transpose_twosided_disp_cat_data.
  Defined.

  (** * 2. The vertical bicategory of the transpose *)
  Definition transpose_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp transpose_ver_sq_bicat.
  Proof.
    split.
    - split.
      + exact (λ (x : B), id_h x).
      + exact (λ (x y z : B)
                 (f : x --> y)
                 (g : y --> z),
               f · g).
    - exact (λ (x y : B) (f g : x --> y), f ==> g).
  Defined.

  Definition transpose_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells transpose_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - intros.
      apply id2.
    - intros.
      apply lunitor.
    - intros.
      apply runitor.
    - intros.
      apply linvunitor.
    - intros.
      apply rinvunitor.
    - intros.
      apply rassociator.
    - intros.
      apply lassociator.
    - exact (λ _ _ _ _ _ τ θ, τ • θ).
    - exact (λ _ _ _ f _ _ τ, f ◃ τ).
    - exact (λ _ _ _ _ _ f τ, τ ▹ f).
  Defined.

  Proposition transpose_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws transpose_ver_sq_bicat_id_comp_cells.
  Proof.
    exact (pr21 ℍ).
  Defined.

  Definition transpose_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact transpose_ver_sq_bicat.
    - exact transpose_ver_sq_bicat_ver_id_comp.
    - exact transpose_ver_sq_bicat_id_comp_cells.
    - exact transpose_ver_sq_bicat_prebicat_laws.
    - exact (pr2 ℍ).
  Defined.

  Definition transpose_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq transpose_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ (x y : B) (v : x -|-> y), id_h_square_bicat v).
    - exact (λ (x₁ y₁ z₁ x₂ y₂ z₂ : B)
               (vx : x₁ -|-> x₂)
               (vy : y₁ -|-> y₂)
               (vz : z₁ -|-> z₂)
               (h₁ : x₁ --> y₁) (h₂ : y₁ --> z₁)
               (k₁ : x₂ --> y₂) (k₂ : y₂ --> z₂)
               (s₁ : square_double_bicat h₁ k₁ vx vy)
               (s₂ : square_double_bicat h₂ k₂ vy vz),
             s₁ ⋆h s₂).
  Defined.

  Definition transpose_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact transpose_ver_bicat_sq_bicat.
    - exact transpose_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  (** *  3. The whiskering operations *)
  Definition transpose_double_bicat_whiskering
    : double_bicat_whiskering transpose_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ (w x y z : B)
               (v₁ : w -|-> x)
               (v₂ : y -|-> z)
               (h₁ h₁' : w --> y)
               (h₂ : x --> z)
               (τ : h₁ ==> h₁')
               (s : square_double_bicat h₁' h₂ v₁ v₂),
             τ ▵s s).
    - exact (λ (w x y z : B)
               (v₁ : w -|-> x)
               (v₂ : y -|-> z)
               (h₁ : w --> y)
               (h₂ h₂' : x --> z)
               (τ : h₂ ==> h₂')
               (s : square_double_bicat h₁ h₂ v₁ v₂),
             τ ▿s s).
    - exact (λ (w x y z : B)
               (v₁ v₁' : w -|-> x)
               (v₂ : y -|-> z)
               (h₁ : w --> y)
               (h₂ : x --> z)
               (τ : v₁ =|=> v₁')
               (s : square_double_bicat h₁ h₂ v₁' v₂),
             τ ◃s s).
    - exact (λ (w x y z : B)
               (v₁ : w -|-> x)
               (v₂ v₂' : y -|-> z)
               (h₁ : w --> y)
               (h₂ : x --> z)
               (τ : v₂ =|=> v₂')
               (s : square_double_bicat h₁ h₂ v₁ v₂),
             τ ▹s s).
  Defined.

  Definition transpose_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact transpose_ver_bicat_sq_bicat_ver_id_comp.
    - exact transpose_double_bicat_whiskering.
  Defined.

  Proposition transpose_whisker_square_bicat_law
    : whisker_square_bicat_law transpose_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply uwhisker_square_id.
    - apply uwhisker_square_comp.
    - apply dwhisker_square_id.
    - apply dwhisker_square_comp.
    - apply lwhisker_square_id.
    - apply lwhisker_square_comp.
    - apply rwhisker_square_id.
    - apply rwhisker_square_comp.
    - apply rwhisker_lwhisker_square.
    - refine (!_).
      apply lwhisker_uwhisker_square.
    - refine (!_).
      apply lwhisker_dwhisker_square.
    - refine (!_).
      apply rwhisker_uwhisker_square.
    - refine (!_).
      apply rwhisker_dwhisker_square.
    - apply dwhisker_uwhisker_square.
    - apply uwhisker_id_v_square.
    - apply lwhisker_id_h_square.
    - apply lwhisker_hcomp_square.
    - apply rwhisker_hcomp_square.
    - apply lrwhisker_hcomp_square.
    - apply uwhisker_vcomp_square.
    - apply dwhisker_vcomp_square.
    - apply ud_whisker_vcomp_square.
  Qed.

  Proposition transpose_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws transpose_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - refine (!_).
      apply double_bicat_interchange.
    - refine (!_).
      apply id_h_square_bicat_id.
    - apply id_v_square_bicat_comp.
    - apply id_h_square_bicat_comp.
  Qed.

  Proposition transpose_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws transpose_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      refine (!_).
      apply lassociator_v_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      apply lassociator_h_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      apply lunitor_v_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      apply lunitor_h_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      apply runitor_v_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      apply runitor_h_comp_square.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q.
      exact (!(hor_bicat_hcomp_h_comp_square B _ _ _ _ _ _ _ _ (!p) (!q))).
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q.
      exact (!(ver_bicat_hcomp_v_comp_square B _ _ _ _ _ _ _ _ (!p) (!q))).
  Qed.

  Proposition transpose_double_bicat_laws
    : double_bicat_laws transpose_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact transpose_whisker_square_bicat_law.
    - exact transpose_double_bicat_id_comp_square_laws.
    - exact transpose_double_bicat_cylinder_laws.
    - intro ; intros.
      apply isaset_square_double_bicat.
  Defined.

  (** * 4. The transpose of a Verity double bicategory *)
  Definition transpose_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact transpose_ver_bicat_sq_id_comp_whisker.
    - exact transpose_double_bicat_laws.
  Defined.
End Transpose.
