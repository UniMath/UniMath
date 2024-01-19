(*****************************************************************************************

 The horizontal dual of a Verity double bicategory

 Given a Verity double bicategory `B`, the horizontal dual is defined as follows:
 - The objects are objects in `B`.
 - Horizontal 1-cells from `x` to `y` are horizontal 1-cells from `y` to `x` in `B`.
 - Vertical 1-cells from `x` to `y` are vertical 1-cells from `x` to `y` in `B`.
 - Horizontal 2-cells are horizontal 2-cells in `B`.
 - Vertical 2-cells from `f` to `g` are vertical 2-cells from `g` to `f` in `B`.
 Note that both the horizontal 1-cells and the vertical 2-cells are reversed. We have to
 reverse the vertical 2-cells to guarantee that the whiskering operations are defined.

 Contents
 1. The data of the horizontal dual
 2. Whiskering operations
 3. Laws of the horizontal dual
 4. The horizontal dual
 5. Vertical cells and squares
 6. The local univalence of the dual

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.

Local Open Scope cat.
Local Open Scope double_bicat.

Section HorizontalDual.
  Context (B : verity_double_bicat).

  Let 𝕍 : bicat := ver_bicat_of_verity_double_bicat B. (* \bV *)

  (** * 1. The data of the horizontal dual *)
  Definition horizontal_dual_hor_bicat
    : bicat
    := op1_bicat (hor_bicat_of_verity_double_bicat B).

  Definition horizontal_dual_twosided_disp_cat_data
    : twosided_disp_cat_data horizontal_dual_hor_bicat horizontal_dual_hor_bicat.
  Proof.
    simple refine ((_ ,, _) ,, (_ ,, _)).
    - exact (λ (x y : B), x -|-> y).
    - exact (λ (x₁ x₂ y₁ y₂ : B)
               (v₁ : x₁ -|-> y₁) (v₂ : x₂ -|-> y₂)
               (h₁ : x₂ --> x₁) (h₂ : y₂ --> y₁),
             square_double_bicat h₁ h₂ v₂ v₁).
    - exact (λ (x y : B) (v : x -|-> y), id_h_square_bicat _).
    - exact (λ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
               (v₁ : x₁ -|-> y₁) (v₂ : x₂ -|-> y₂) (v₃ : x₃ -|-> y₃)
               (h₁ : x₂ --> x₁) (h₂ : x₃ --> x₂)
               (k₁ : y₂ --> y₁) (k₂ : y₃ --> y₂)
               (s₁ : square_double_bicat h₁ k₁ v₂ v₁)
               (s₂ : square_double_bicat h₂ k₂ v₃ v₂),
             s₂ ⋆h s₁).
  Defined.

  Definition horizontal_dual_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact horizontal_dual_hor_bicat.
    - exact horizontal_dual_twosided_disp_cat_data.
  Defined.

  Definition horizontal_dual_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp horizontal_dual_ver_sq_bicat.
  Proof.
    repeat split ; cbn.
    - exact (λ (x : B), id_v x).
    - exact (λ (x y z : B)
               (v₁ : x -|-> y) (v₂ : y -|-> z),
             v₁ · v₂).
    - exact (λ (x y : B)
               (v₁ v₂ : x -|-> y),
             v₂ =|=> v₁).
  Defined.

  Definition horizontal_dual_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells horizontal_dual_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - exact (λ (x y : B) (v : x -|-> y), id2 v).
    - exact (λ (x y : B) (v : x -|-> y), lunitor (C := op2_bicat 𝕍) v).
    - exact (λ (x y : B) (v : x -|-> y), runitor (C := op2_bicat 𝕍) v).
    - exact (λ (x y : B) (v : x -|-> y), linvunitor (C := op2_bicat 𝕍) v).
    - exact (λ (x y : B) (v : x -|-> y), rinvunitor (C := op2_bicat 𝕍) v).
    - exact (λ (w x y z : B)
               (v₁ : w -|-> x) (v₂ : x -|-> y) (v₃ : y -|-> z),
             rassociator (C := op2_bicat 𝕍) v₁ v₂ v₃).
    - exact (λ (w x y z : B)
               (v₁ : w -|-> x) (v₂ : x -|-> y) (v₃ : y -|-> z),
             lassociator (C := op2_bicat 𝕍) v₁ v₂ v₃).
    - exact (λ (x y : B)
               (v₁ v₂ v₃ : x -|-> y)
               (τ : v₂ =|=> v₁) (θ : v₃ =|=> v₂),
             θ • τ).
    - exact (λ (x y z : B)
               (v : x -|-> y)
               (w₁ w₂ : y -|-> z)
               (τ : w₂ =|=> w₁),
             v ◃ τ).
    - exact (λ (x y z : B)
               (v₁ v₂ : x -|-> y)
               (w : y -|-> z)
               (τ : v₂ =|=> v₁),
             τ ▹ w).
  Defined.

  Proposition horizontal_dual_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws horizontal_dual_ver_sq_bicat_id_comp_cells.
  Proof.
    exact (pr21 (op2_bicat 𝕍)).
  Qed.

  Definition horizontal_dual_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact horizontal_dual_ver_sq_bicat.
    - exact horizontal_dual_ver_sq_bicat_ver_id_comp.
    - exact horizontal_dual_ver_sq_bicat_id_comp_cells.
    - exact horizontal_dual_ver_sq_bicat_prebicat_laws.
    - abstract
        (intro ; intros ;
         apply cellset_property).
  Defined.

  Definition horizontal_dual_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq horizontal_dual_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ (x y : B) (h : y --> x), id_v_square_bicat h).
    - exact (λ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
               (h₁ : y₁ --> x₁)
               (h₂ : y₂ --> x₂)
               (h₃ : y₃ --> x₃)
               (v₁ : x₁ -|-> x₂) (v₂ : x₂ -|-> x₃)
               (w₁ : y₁ -|-> y₂) (w₂ : y₂ -|-> y₃)
               (s₁ : square_double_bicat h₁ h₂ w₁ v₁)
               (s₂ : square_double_bicat h₂ h₃ w₂ v₂),
             s₁ ⋆v s₂).
  Defined.

  Definition horizontal_dual_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact horizontal_dual_ver_bicat_sq_bicat.
    - exact horizontal_dual_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  (** * 2. Whiskering operations *)
  Definition horizontal_dual_double_bicat_whiskering
    : double_bicat_whiskering horizontal_dual_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ (w x y z : B)
               (h₁ : x --> w)
               (h₂ : z --> y)
               (v₁ v₁' : w -|-> y)
               (v₂ : x -|-> z)
               (τ : v₁' =|=> v₁)
               (s : square_double_bicat h₁ h₂ v₂ v₁'),
             τ ▹s s).
    - exact (λ (w x y z : B)
               (h₁ : x --> w)
               (h₂ : z --> y)
               (v₁ : w -|-> y)
               (v₂ v₂' : x -|-> z)
               (τ : v₂' =|=> v₂)
               (s : square_double_bicat h₁ h₂ v₂ v₁),
             τ ◃s s).
    - exact (λ (w x y z : B)
               (h₁ h₁' : x --> w)
               (h₂ : z --> y)
               (v₁ : w -|-> y)
               (v₂ : x -|-> z)
               (τ : h₁ ==> h₁')
               (s : square_double_bicat h₁' h₂ v₂ v₁),
             τ ▵s s).
    - exact (λ (w x y z : B)
               (h₁ : x --> w)
               (h₂ h₂' : z --> y)
               (v₁ : w -|-> y)
               (v₂ : x -|-> z)
               (τ : h₂ ==> h₂')
               (s : square_double_bicat h₁ h₂ v₂ v₁),
             τ ▿s s).
  Defined.

  Definition horizontal_dual_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact horizontal_dual_ver_bicat_sq_bicat_ver_id_comp.
    - exact horizontal_dual_double_bicat_whiskering.
  Defined.

  (** * 3. Laws of the horizontal dual *)
  Proposition horizontal_dual_whisker_square_bicat_law
    : whisker_square_bicat_law horizontal_dual_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply rwhisker_square_id.
    - apply rwhisker_square_comp.
    - apply lwhisker_square_id.
    - apply lwhisker_square_comp.
    - apply uwhisker_square_id.
    - apply uwhisker_square_comp.
    - apply dwhisker_square_id.
    - apply dwhisker_square_comp.
    - apply dwhisker_uwhisker_square.
    - apply rwhisker_uwhisker_square.
    - apply lwhisker_uwhisker_square.
    - apply rwhisker_dwhisker_square.
    - apply lwhisker_dwhisker_square.
    - refine (!_).
      apply rwhisker_lwhisker_square.
    - refine (!_).
      apply lwhisker_id_h_square.
    - apply uwhisker_id_v_square.
    - apply uwhisker_vcomp_square.
    - apply dwhisker_vcomp_square.
    - apply ud_whisker_vcomp_square.
    - apply rwhisker_hcomp_square.
    - apply lwhisker_hcomp_square.
    - refine (!_).
      apply lrwhisker_hcomp_square.
  Qed.

  Proposition horizontal_dual_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws horizontal_dual_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply double_bicat_interchange.
    - apply id_h_square_bicat_id.
    - apply id_h_square_bicat_comp.
    - apply id_v_square_bicat_comp.
  Qed.

  Proposition horizontal_dual_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws horizontal_dual_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      etrans.
      {
        apply maponpaths.
        apply lassociator_h_comp_square''.
      }
      rewrite <- dwhisker_square_comp.
      rewrite lassociator_rassociator.
      apply dwhisker_square_id.
    - intro ; intros ; cbn.
      etrans.
      {
        apply maponpaths.
        apply lassociator_v_comp_square'.
      }
      rewrite <- rwhisker_lwhisker_square.
      rewrite <- rwhisker_square_comp.
      rewrite (lassociator_rassociator (C := 𝕍)).
      apply rwhisker_square_id.
    - intro ; intros ; cbn.
      apply runitor_h_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply lunitor_v_comp_square'.
      }
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_square_comp.
      rewrite (linvunitor_lunitor (C := 𝕍)).
      apply lwhisker_square_id.
    - intro ; intros ; cbn.
      apply lunitor_h_comp_square.
    - intro ; intros ; cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply runitor_v_comp_square'.
      }
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_square_comp.
      rewrite (rinvunitor_runitor (C := 𝕍)).
      apply lwhisker_square_id.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q ; cbn.
      rewrite <- !(vcomp_whisker (C := 𝕍)).
      exact (!(ver_bicat_hcomp_v_comp_square B _ _ _ _ _ _ _ _ (!p) (!q))).
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q ; cbn.
      rewrite <- !vcomp_whisker.
      exact (hor_bicat_hcomp_h_comp_square B _ _ _ _ _ _ _ _ q p).
  Qed.

  Proposition horizontal_dual_double_bicat_laws
    : double_bicat_laws horizontal_dual_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact horizontal_dual_whisker_square_bicat_law.
    - exact horizontal_dual_double_bicat_id_comp_square_laws.
    - exact horizontal_dual_double_bicat_cylinder_laws.
    - intro ; intros.
      apply isaset_square_double_bicat.
  Qed.

  (** * 4. The horizontal dual *)
  Definition horizontal_dual_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact horizontal_dual_ver_bicat_sq_id_comp_whisker.
    - exact horizontal_dual_double_bicat_laws.
  Defined.

  (** * 5. Vertical cells and squares *)
  Definition horizontal_dual_vertically_saturated
             (H : vertically_saturated B)
    : vertically_saturated horizontal_dual_verity_double_bicat.
  Proof.
    refine (λ (x y : B) (v₁ v₂ : x -|-> y), _).
    use isweq_iso.
    - exact (λ s, square_to_vertical_cell H s).
    - abstract
        (intro τ ; cbn ;
         refine (_ @ vertical_cell_to_square_to_vertical_cell H τ) ;
         apply maponpaths ; unfold vertical_cell_to_square ;
         rewrite lwhisker_id_h_square ;
         apply idpath).
    - abstract
        (intro s ; cbn ;
         refine (_ @ square_to_vertical_cell_to_square H s) ;
         unfold vertical_cell_to_square ;
         rewrite lwhisker_id_h_square ;
         apply idpath).
  Defined.

  (** * 6. The local univalence of the dual *)
  Proposition hor_locally_univalent_horizontal_dual
              (H : hor_locally_univalent B)
    : hor_locally_univalent horizontal_dual_verity_double_bicat.
  Proof.
    use op1_bicat_is_univalent_2_1.
    exact H.
  Qed.

  Definition horizontal_dual_inv2cell_weq
             {x y : B}
             (v₁ v₂ : x -|-> y)
    : invertible_2cell (C := 𝕍) v₁ v₂
      ≃
      invertible_2cell
        (C := ver_bicat_of_verity_double_bicat horizontal_dual_verity_double_bicat)
        v₁ v₂.
  Proof.
    use weq_iso.
    - use (λ τ, make_invertible_2cell _).
      + exact (τ^-1).
      + use make_is_invertible_2cell.
        * exact τ.
        * exact (vcomp_rinv τ).
        * exact (vcomp_linv τ).
    - use (λ τ, make_invertible_2cell _).
      + exact (τ^-1).
      + use make_is_invertible_2cell.
        * exact τ.
        * exact (vcomp_rinv τ).
        * exact (vcomp_linv τ).
    - abstract
        (intro ;
         apply idpath).
    - abstract
        (intro ;
         apply idpath).
  Defined.

  Proposition ver_locally_univalent_horizontal_dual
              (H : ver_locally_univalent B)
    : ver_locally_univalent horizontal_dual_verity_double_bicat.
  Proof.
    intros x y v₁ v₂.
    use weqhomot.
    - exact (horizontal_dual_inv2cell_weq v₁ v₂
             ∘ make_weq _ (H x y v₁ v₂))%weq.
    - intro p.
      induction p.
      use cell_from_invertible_2cell_eq ; cbn.
      apply idpath.
  Qed.

  Proposition locally_univalent_horizontal_dual
              (H : locally_univalent_verity_double_bicat B)
    : locally_univalent_verity_double_bicat horizontal_dual_verity_double_bicat.
  Proof.
    split.
    - use hor_locally_univalent_horizontal_dual.
      apply H.
    - use ver_locally_univalent_horizontal_dual.
      apply H.
  Qed.
End HorizontalDual.
