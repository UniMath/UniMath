(*************************************************************************************

 Symmetrically univalent double categories

 The notion of univalence for pseudo double categories is as follows:
 - The vertical category is required to be univalent
 - The 2-sided displayed category of horizontal morphisms and squares is required to
   be univalent
 This is not a symmetric notion: horizontal morphisms and vertical morphisms have
 different requirements. In this file, we consider a stronger notion of univalence
 that is symmetric. The added requirements are that the horizontal category is univalent
 and that the 2-sided displayed category of vertical morphisms and squares is univalent
 as well. We also require that the horizontal morphisms form a set.

 One application of this notion of univalence is that we can define the dual of a
 pseudo double category: we can switch the vertical and the horizontal morphisms.
 Symmetric univalent double categories are those for which this dual is actually a
 univalent double category.

 Contents
 1. The horizontal category
 2. The 2-sided displayed category of vertical morphisms and squares
 3. A useful lemma for `idtoiso`
 4. Horizontal identities
 5. Horizontal composition
 6. The left unitor
 7. The right unitor
 8. The associator
 9. The triangle and pentagon equations
 10. The dual double category
 11. Symmetric univalence for double categories

 *************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Comma.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCatsLaws.
Import DoubleCatsLaws.TransportSquare.

Local Open Scope cat.
Local Open Scope double_cat.

Section DualPseudoDoubleCat.
  Context (C : double_cat)
          (HC : ∏ (x y : C), isaset (x -->h y)).

  (** * 1. The horizontal category *)
  Definition dual_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, x -->h y).
  Defined.

  Definition dual_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact dual_precategory_ob_mor.
    - cbn.
      exact (λ x, identity_h x).
    - exact (λ x y z f g, f ·h g).
  Defined.

  Proposition dual_precategory_laws
    : is_precategory dual_precategory_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split ; cbn.
    - intros x y h.
      use globular_iso_square_to_path.
      apply lunitor_globural_iso_square.
    - intros x y h.
      use globular_iso_square_to_path.
      apply runitor_globural_iso_square.
    - intros w x y z h₁ h₂ h₃.
      use globular_iso_square_to_path.
      apply associator_globural_iso_square.
  Defined.

  Definition dual_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact dual_precategory_data.
    - exact dual_precategory_laws.
  Defined.

  Definition dual_category
    : category.
  Proof.
    use make_category.
    - exact dual_precategory.
    - exact HC.
  Defined.

  (** * 2. The 2-sided displayed category of vertical morphisms and squares *)
  Definition dual_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor dual_category dual_category.
  Proof.
    simple refine (_ ,, _).
    - cbn.
      exact (λ x y, x -->v y).
    - exact (λ x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂, square v₁ v₂ h₁ h₂).
  Defined.

  Definition dual_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp dual_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x y f, id_h_square f).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ vx₁ vx₂ vy₁ vy₂ s₁ s₂, _).
      cbn in s₁, s₂ ; cbn.
      exact (s₁ ⋆h s₂).
  Defined.

  Definition dual_twosided_disp_cat_data
    : twosided_disp_cat_data dual_category dual_category.
  Proof.
    simple refine (_ ,, _).
    - exact dual_twosided_disp_cat_ob_mor.
    - exact dual_twosided_disp_cat_id_comp.
  Defined.

  Proposition transportb_disp_mor2_dual
              {x₁ x₂ y₁ y₂ : dual_category}
              {h h' : x₁ --> x₂}
              {k k' : y₁ --> y₂}
              {v₁ : dual_twosided_disp_cat_data x₁ y₁}
              {v₂ : dual_twosided_disp_cat_data x₂ y₂}
              (p : h = h')
              (q : k = k')
              (s : v₁ -->[ h' ][ k' ] v₂)
    : transportb_disp_mor2 p q s
      =
      transportf_square
        (id_v_right _ @ id_v_left _)
        (id_v_right _ @ id_v_left _)
        (path_to_globular_iso_square p ⋆v s ⋆v path_to_globular_iso_square (!q)).
  Proof.
    induction p, q ; cbn.
    rewrite <- !path_to_globular_iso_square_id.
    rewrite square_id_right_v.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite !transportf_f_square.
    refine (!_).
    apply transportf_square_id.
  Qed.

  Proposition dual_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms dual_twosided_disp_cat_data.
  Proof.
    repeat split.
    - unfold id_two_disp_left_law ; cbn.
      intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
      etrans.
      {
        refine (!_).
        apply square_id_right_v'.
      }
      rewrite <- lunitor_linvunitor_h'.
      rewrite transportb_disp_mor2_dual.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- path_to_globular_iso_square_inv.
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite lunitor_square.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - unfold id_two_disp_right_law ; cbn.
      intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
      etrans.
      {
        refine (!_).
        apply square_id_right_v'.
      }
      rewrite <- runitor_rinvunitor_h'.
      rewrite transportb_disp_mor2_dual.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- path_to_globular_iso_square_inv.
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite runitor_square.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - unfold assoc_two_disp_law ; cbn.
      intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ v₁ v₂ v₃ v₄ h₁ h₂ h₃ k₁ k₂ k₃ s₁ s₂ s₃.
      etrans.
      {
        refine (!_).
        apply square_id_right_v'.
      }
      rewrite <- lassociator_rassociator_h'.
      rewrite transportb_disp_mor2_dual.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- path_to_globular_iso_square_inv.
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite lassociator_square.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂.
      apply isaset_square.
  Qed.

  Definition dual_twosided_disp_cat
    : twosided_disp_cat dual_category dual_category.
  Proof.
    simple refine (_ ,, _).
    - exact dual_twosided_disp_cat_data.
    - exact dual_twosided_disp_cat_axioms.
  Defined.

  (** * 3. A useful lemma for `idtoiso` *)
  Proposition idtoiso_twosided_disp_dual
              {x y : C}
              {v₁ v₂ : x -->v y}
              (p : v₁ = v₂)
    : pr1 (idtoiso_twosided_disp (D := dual_twosided_disp_cat) (idpath _) (idpath _) p)
      =
      transportf_square
        (idpath _)
        p
        (id_h_square v₁).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  (** * 4. Horizontal identities *)
  Definition dual_hor_id_data
    : hor_id_data dual_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - cbn.
      exact (λ x, identity_v x).
    - exact (λ x y h, id_v_square h).
  Defined.

  Proposition dual_hor_id_laws
    : hor_id_laws dual_hor_id_data.
  Proof.
    split ; cbn.
    - intro x.
      rewrite id_h_square_id.
      apply idpath.
    - intros x y z h k.
      rewrite comp_h_square_id.
      apply idpath.
  Qed.

  Definition dual_hor_id
    : hor_id dual_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact dual_hor_id_data.
    - exact dual_hor_id_laws.
  Defined.

  (** * 5. Horizontal composition *)
  Definition dual_hor_comp_data
    : hor_comp_data dual_twosided_disp_cat.
  Proof.
    use make_hor_comp_data.
    - cbn.
      exact (λ x y z v₁ v₂, v₁ ·v v₂).
    - cbn.
      exact (λ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₂ w₁ w₂ s₁ s₂, s₁ ⋆v s₂).
  Defined.

  Proposition dual_hor_comp_laws
    : hor_comp_laws dual_hor_comp_data.
  Proof.
    split ; cbn.
    - intros x y z v w.
      rewrite id_h_square_comp.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ h₁ h₁' h₂ h₂' h₃ h₃' u₁ u₂ v₁ v₂ w₁ w₂ s₁ s₁' s₂ s₂'.
      rewrite comp_h_square_comp.
      apply idpath.
  Qed.

  Definition dual_hor_comp
    : hor_comp dual_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact dual_hor_comp_data.
    - exact dual_hor_comp_laws.
  Defined.

  (** * 6. The left unitor *)
  Definition dual_lunitor_data
    : double_lunitor_data dual_hor_id dual_hor_comp.
  Proof.
    intros x y f ; cbn ; cbn in x, y, f.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply id_left.
  Defined.

  Arguments dual_lunitor_data /.

  Proposition dual_lunitor_laws
    : double_lunitor_laws dual_lunitor_data.
  Proof.
    unfold double_lunitor_laws ; cbn -[idtoiso_twosided_disp].
    intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
    rewrite square_id_left_v.
    rewrite transportb_disp_mor2_dual.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- path_to_globular_iso_square_comp.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !path_to_globular_iso_square_inv.
    etrans.
    {
      do 4 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_inv.
    }
    rewrite !globular_iso_to_path_to_iso.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite !transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply lunitor_square.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply square_assoc_v'.
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply linvunitor_lunitor_h.
    }
    unfold transportb_square.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply runitor_square'.
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply runitor_rinvunitor_h.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_f_square.
    use transportf_square_eq.
    apply maponpaths.
    rewrite id_h_square_comp.
    rewrite id_h_square_id.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Definition dual_lunitor
    : double_cat_lunitor dual_hor_id dual_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact dual_lunitor_data.
    - exact dual_lunitor_laws.
  Defined.

  (** * 7. The right unitor *)
  Definition dual_runitor_data
    : double_runitor_data dual_hor_id dual_hor_comp.
  Proof.
    intros x y f ; cbn ; cbn in x, y, f.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply id_right.
  Defined.

  Arguments dual_runitor_data /.

  Proposition dual_runitor_laws
    : double_runitor_laws dual_runitor_data.
  Proof.
    unfold double_runitor_laws ; cbn -[idtoiso_twosided_disp].
    intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
    rewrite square_id_right_v.
    rewrite transportb_disp_mor2_dual.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- path_to_globular_iso_square_comp.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !path_to_globular_iso_square_inv.
    etrans.
    {
      do 4 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_inv.
    }
    rewrite !globular_iso_to_path_to_iso.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite !transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply lunitor_square.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply square_assoc_v'.
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply linvunitor_lunitor_h.
    }
    unfold transportb_square.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply runitor_square'.
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply runitor_rinvunitor_h.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_f_square.
    use transportf_square_eq.
    apply maponpaths.
    rewrite id_h_square_comp.
    rewrite id_h_square_id.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Definition dual_runitor
    : double_cat_runitor dual_hor_id dual_hor_comp.
  Proof.
    use make_double_runitor.
    - exact dual_runitor_data.
    - exact dual_runitor_laws.
  Defined.

  (** * 8. The associator *)
  Definition dual_associator_data
    : double_associator_data dual_hor_comp.
  Proof.
    intros w x y z v₁ v₂ v₃ ; cbn.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply assoc.
  Defined.

  Arguments dual_associator_data /.

  Proposition dual_associator_laws
    : double_associator_laws dual_associator_data.
  Proof.
    unfold double_associator_laws ; cbn -[idtoiso_twosided_disp].
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ v₄ v₅ v₆ h₁ h₂ h₃ h₄ s₁ s₂ s₃.
    rewrite square_assoc_v.
    rewrite transportb_disp_mor2_dual.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- path_to_globular_iso_square_comp.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !path_to_globular_iso_square_inv.
    etrans.
    {
      do 4 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_inv.
    }
    rewrite !globular_iso_to_path_to_iso.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite !transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply lunitor_square.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply square_assoc_v'.
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply linvunitor_lunitor_h.
    }
    unfold transportb_square.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply runitor_square'.
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply runitor_rinvunitor_h.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportf_hcomp_l.
    rewrite transportf_f_square.
    use transportf_square_eq.
    apply maponpaths.
    rewrite !id_h_square_comp.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Definition dual_associator
    : double_cat_associator dual_hor_comp.
  Proof.
    use make_double_associator.
    - exact dual_associator_data.
    - exact dual_associator_laws.
  Defined.

  (** * 9. The triangle and pentagon equations *)
  Proposition dual_triangle_law
    : triangle_law dual_lunitor dual_runitor dual_associator.
  Proof.
    unfold triangle_law.
    unfold double_associator, double_lunitor, double_runitor.
    cbn -[idtoiso_twosided_disp].
    intros x y z v w.
    etrans.
    {
      apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportb_disp_mor2_dual.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_inv.
    }
    rewrite !globular_iso_to_path_to_iso.
    rewrite transportf_square_prewhisker.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply lunitor_square'.
    }
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply lunitor_linvunitor_h.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite !id_h_square_comp.
    rewrite !id_h_square_id.
    rewrite square_id_right_v.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite !transportf_square_prewhisker.
    rewrite !transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite !transportf_hcomp_r.
    rewrite !transportf_f_square.
    use transportf_square_eq.
    apply maponpaths_2.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Proposition dual_pentagon_law
    : pentagon_law dual_associator.
  Proof.
    unfold pentagon_law ; cbn.
    unfold double_associator.
    cbn -[idtoiso_twosided_disp].
    intros v w x y z v₁ v₂ v₃ v₄.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply idtoiso_twosided_disp_dual.
      }
      apply maponpaths_2.
      apply idtoiso_twosided_disp_dual.
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply idtoiso_twosided_disp_dual.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply idtoiso_twosided_disp_dual.
      }
      apply maponpaths_2.
      apply maponpaths.
      apply idtoiso_twosided_disp_dual.
    }
    rewrite transportb_disp_mor2_dual.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_inv.
    }
    rewrite !globular_iso_to_path_to_iso.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply runitor_square'.
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply runitor_rinvunitor_h.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite !transportf_hcomp_l.
    rewrite !transportf_f_square.
    use transportf_square_eq.
    rewrite <- !id_h_square_comp.
    rewrite transportf_square_id.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply transportf_square_id_h_square_eq'.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply transportf_square_id_h_square_eq'.
    }
    etrans.
    {
      apply maponpaths.
      apply transportf_square_id_h_square_eq'.
    }
    use eq_hcomp_square.
    - abstract
        (rewrite !assocl_v ;
         apply idpath).
    - refine (!_).
      etrans.
      {
        refine (!_).
        apply (transportf_hcomp_r (idpath _)).
      }
      apply maponpaths.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - apply transportf_square_id_h_square_eq.
  Qed.

  (** * 10. The dual double category *)
  Definition dual_double_cat
             (HC' : is_univalent dual_category)
             (HC'' : is_univalent_twosided_disp_cat dual_twosided_disp_cat)
    : double_cat.
  Proof.
    use make_double_cat.
    - exact dual_category.
    - exact dual_twosided_disp_cat.
    - exact dual_hor_id.
    - exact dual_hor_comp.
    - exact dual_lunitor.
    - exact dual_runitor.
    - exact dual_associator.
    - exact dual_triangle_law.
    - exact dual_pentagon_law.
    - exact HC'.
    - exact HC''.
  Defined.
End DualPseudoDoubleCat.

(** * 11. Symmetric univalence for double categories *)
Definition symmetric_univalent
           (C : double_cat)
  : UU
  := ∑ (HC : ∏ (x y : C), isaset (x -->h y)),
     is_univalent (dual_category C HC)
     ×
     is_univalent_twosided_disp_cat (dual_twosided_disp_cat C HC).

Definition make_symmetric_univalent
           {C : double_cat}
           (H₁ : ∏ (x y : C), isaset (x -->h y))
           (H₂ : is_univalent (dual_category C H₁))
           (H₃ : is_univalent_twosided_disp_cat (dual_twosided_disp_cat C H₁))
  : symmetric_univalent C
  := H₁ ,, H₂ ,, H₃.
