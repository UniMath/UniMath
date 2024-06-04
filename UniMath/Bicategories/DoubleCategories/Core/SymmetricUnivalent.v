(*************************************************************************************

 Symmetrically univalent double categories

 The notion of univalence for pseudo double categories is as follows:
 - The vertical category is required to be univalent
 - The 2-sided displayed category of horizontal morphisms and squares is required to
   be univalent
 This is not a symmetric notion: horizontal morphisms and vertical morphisms play a
 different role in this definition. However, in some examples a stronger requirement
 is satisfied.

 Let us look at the double category of squares in aunivalent  category `C`. This
 double category is defined as follows:
 - Objects: objects in `C`
 - Vertical morphisms: morphisms in `C`
 - Horizontal morphisms: morphisms in `C`
 - Squares: commutative squares in `C`
 For this double category, we both have a univalent category of objects and vertical
 morphisms and of objects and horizontal morphisms. In addition, both the categories of
 vertical morphisms and squares and of horizontal morphisms and squares are univalent.
 This gives a stronger notion of univalence for double categories, which we call
 symmetric univalence.

 In this file, we define this notion. To do so, we first define the transpose of a
 pseudo double category ([transpose_double_cat]). To construct this transpose, we first
 assume that the horizontal morphisms in `C` forms a set. In order to guarantee that the
 transpose is a univalent pseudo double category, we need to add two requirements:
 1. The category of objects and horizontal morphisms is univalent
 2. The category of vertical morphisms and squares is univalent
 Symmetric univalence is the conjunction of these requirements.

 Note that we explicitly assume that the horizontal morphisms form a set in our definition
 of symmetric univalence ([symmetric_univalent]) even though it follows from the univalence
 conditions. The reason for that is that we want to reuse the notions of univalence that
 we defined for categories and for 2-sided displayed categories. These two notions
 already have the requirement that the morphisms for a set in them, so in order to use
 them, we must have that the horizontal morphisms form a set.

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
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.
Import TransportSquare.

Local Open Scope cat.
Local Open Scope double_cat.

Section TransposePseudoDoubleCat.
  Context (C : univalent_double_cat)
          (HC : ∏ (x y : C), isaset (x -->h y)).

  (** * 1. The horizontal category *)
  Definition transpose_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, x -->h y).
  Defined.

  Definition transpose_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact transpose_precategory_ob_mor.
    - cbn.
      exact (λ x, identity_h (C := C) x).
    - exact (λ x y z f g, f ·h g).
  Defined.

  Proposition transpose_precategory_laws
    : is_precategory transpose_precategory_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split ; cbn.
    - intros x y h.
      use globular_iso_square_to_path.
      apply lunitor_globular_iso_square.
    - intros x y h.
      use globular_iso_square_to_path.
      apply runitor_globular_iso_square.
    - intros w x y z h₁ h₂ h₃.
      use globular_iso_square_to_path.
      apply associator_globular_iso_square.
  Defined.

  Definition transpose_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact transpose_precategory_data.
    - exact transpose_precategory_laws.
  Defined.

  Definition transpose_category
    : category.
  Proof.
    use make_category.
    - exact transpose_precategory.
    - exact HC.
  Defined.

  (** * 2. The 2-sided displayed category of vertical morphisms and squares *)
  Definition transpose_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor transpose_category transpose_category.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x y : C), x -->v y).
    - exact (λ x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂, square v₁ v₂ h₁ h₂).
  Defined.

  Definition transpose_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp transpose_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x y f, id_h_square f).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ vx₁ vx₂ vy₁ vy₂ s₁ s₂, _).
      cbn in s₁, s₂ ; cbn.
      exact (s₁ ⋆h s₂).
  Defined.

  Definition transpose_twosided_disp_cat_data
    : twosided_disp_cat_data transpose_category transpose_category.
  Proof.
    simple refine (_ ,, _).
    - exact transpose_twosided_disp_cat_ob_mor.
    - exact transpose_twosided_disp_cat_id_comp.
  Defined.

  Proposition transportb_disp_mor2_transpose
              {x₁ x₂ y₁ y₂ : transpose_category}
              {h h' : x₁ --> x₂}
              {k k' : y₁ --> y₂}
              {v₁ : transpose_twosided_disp_cat_data x₁ y₁}
              {v₂ : transpose_twosided_disp_cat_data x₂ y₂}
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
    cbn in h, k.
    rewrite <- !(path_to_globular_iso_square_id (C := C)).
    rewrite square_id_right_v.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite !transportf_f_square.
    refine (!_).
    apply transportf_square_id.
  Qed.

  Proposition transpose_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms transpose_twosided_disp_cat_data.
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
      rewrite transportb_disp_mor2_transpose.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- (path_to_globular_iso_square_inv (C := C)).
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply (square_assoc_v (C := C)).
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
      rewrite transportb_disp_mor2_transpose.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- (path_to_globular_iso_square_inv (C := C)).
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply (square_assoc_v (C := C)).
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
      rewrite transportb_disp_mor2_transpose.
      rewrite !globular_iso_to_path_to_iso.
      cbn.
      rewrite <- (path_to_globular_iso_square_inv (C := C)).
      rewrite globular_iso_to_path_to_iso.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply (square_assoc_v (C := C)).
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

  Definition transpose_twosided_disp_cat
    : twosided_disp_cat transpose_category transpose_category.
  Proof.
    simple refine (_ ,, _).
    - exact transpose_twosided_disp_cat_data.
    - exact transpose_twosided_disp_cat_axioms.
  Defined.

  (** * 3. A useful lemma for `idtoiso` *)
  Proposition idtoiso_twosided_disp_transpose
              {x y : C}
              {v₁ v₂ : x -->v y}
              (p : v₁ = v₂)
    : pr1 (idtoiso_twosided_disp (D := transpose_twosided_disp_cat) (idpath _) (idpath _) p)
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
  Definition transpose_hor_id_data
    : hor_id_data transpose_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - exact (λ x, identity_v (C := C) x).
    - exact (λ x y h, id_v_square h).
  Defined.

  Proposition transpose_hor_id_laws
    : hor_id_laws transpose_hor_id_data.
  Proof.
    split ; cbn.
    - intro x.
      rewrite id_h_square_id.
      apply idpath.
    - intros x y z h k.
      rewrite comp_h_square_id.
      apply idpath.
  Qed.

  Definition transpose_hor_id
    : hor_id transpose_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact transpose_hor_id_data.
    - exact transpose_hor_id_laws.
  Defined.

  (** * 5. Horizontal composition *)
  Definition transpose_hor_comp_data
    : hor_comp_data transpose_twosided_disp_cat.
  Proof.
    use make_hor_comp_data.
    - cbn.
      exact (λ x y z v₁ v₂, v₁ ·v v₂).
    - cbn.
      exact (λ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₂ w₁ w₂ s₁ s₂, s₁ ⋆v s₂).
  Defined.

  Proposition transpose_hor_comp_laws
    : hor_comp_laws transpose_hor_comp_data.
  Proof.
    split ; cbn.
    - intros x y z v w.
      rewrite id_h_square_comp.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ h₁ h₁' h₂ h₂' h₃ h₃' u₁ u₂ v₁ v₂ w₁ w₂ s₁ s₁' s₂ s₂'.
      rewrite comp_h_square_comp.
      apply idpath.
  Qed.

  Definition transpose_hor_comp
    : hor_comp transpose_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact transpose_hor_comp_data.
    - exact transpose_hor_comp_laws.
  Defined.

  (** * 6. The left unitor *)
  Definition transpose_lunitor_data
    : double_lunitor_data transpose_hor_id transpose_hor_comp.
  Proof.
    intros x y f ; cbn ; cbn in x, y, f.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply id_left.
  Defined.

  Arguments transpose_lunitor_data /.

  Proposition transpose_lunitor_laws
    : double_lunitor_laws transpose_lunitor_data.
  Proof.
    unfold double_lunitor_laws ; cbn -[idtoiso_twosided_disp].
    intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
    rewrite square_id_left_v.
    rewrite transportb_disp_mor2_transpose.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- (path_to_globular_iso_square_comp (C := C)).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !(path_to_globular_iso_square_inv (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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
      apply (lunitor_square (C := C)).
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
      apply (runitor_square' (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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

  Definition transpose_lunitor
    : double_cat_lunitor transpose_hor_id transpose_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact transpose_lunitor_data.
    - exact transpose_lunitor_laws.
  Defined.

  (** * 7. The right unitor *)
  Definition transpose_runitor_data
    : double_runitor_data transpose_hor_id transpose_hor_comp.
  Proof.
    intros x y f ; cbn ; cbn in x, y, f.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply id_right.
  Defined.

  Arguments transpose_runitor_data /.

  Proposition transpose_runitor_laws
    : double_runitor_laws transpose_runitor_data.
  Proof.
    unfold double_runitor_laws ; cbn -[idtoiso_twosided_disp].
    intros x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂ s.
    rewrite square_id_right_v.
    rewrite transportb_disp_mor2_transpose.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- (path_to_globular_iso_square_comp (C := C)).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !(path_to_globular_iso_square_inv (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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
      apply (lunitor_square (C := C)).
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
      apply (runitor_square' (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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

  Definition transpose_runitor
    : double_cat_runitor transpose_hor_id transpose_hor_comp.
  Proof.
    use make_double_runitor.
    - exact transpose_runitor_data.
    - exact transpose_runitor_laws.
  Defined.

  (** * 8. The associator *)
  Definition transpose_associator_data
    : double_associator_data transpose_hor_comp.
  Proof.
    intros w x y z v₁ v₂ v₃ ; cbn.
    refine (idtoiso_twosided_disp (idpath _) (idpath _) _).
    apply assoc.
  Defined.

  Arguments transpose_associator_data /.

  Proposition transpose_associator_laws
    : double_associator_laws transpose_associator_data.
  Proof.
    unfold double_associator_laws ; cbn -[idtoiso_twosided_disp].
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ v₄ v₅ v₆ h₁ h₂ h₃ h₄ s₁ s₂ s₃.
    rewrite square_assoc_v.
    rewrite transportb_disp_mor2_transpose.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- (path_to_globular_iso_square_comp (C := C)).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply path_to_globular_iso_square_comp.
    }
    rewrite <- !(path_to_globular_iso_square_inv (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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
      apply (lunitor_square (C := C)).
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
      apply (runitor_square' (C := C)).
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
      apply idtoiso_twosided_disp_transpose.
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

  Definition transpose_associator
    : double_cat_associator transpose_hor_comp.
  Proof.
    use make_double_associator.
    - exact transpose_associator_data.
    - exact transpose_associator_laws.
  Defined.

  (** * 9. The triangle and pentagon equations *)
  Proposition transpose_triangle_law
    : triangle_law transpose_lunitor transpose_runitor transpose_associator.
  Proof.
    unfold triangle_law.
    unfold double_associator, double_lunitor, double_runitor.
    cbn -[idtoiso_twosided_disp].
    intros x y z v w.
    etrans.
    {
      apply maponpaths_2.
      apply idtoiso_twosided_disp_transpose.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply idtoiso_twosided_disp_transpose.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply idtoiso_twosided_disp_transpose.
    }
    rewrite transportb_disp_mor2_transpose.
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
      apply (lunitor_square' (C := C)).
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

  Proposition transpose_pentagon_law
    : pentagon_law transpose_associator.
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
        apply idtoiso_twosided_disp_transpose.
      }
      apply maponpaths_2.
      apply idtoiso_twosided_disp_transpose.
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply idtoiso_twosided_disp_transpose.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply idtoiso_twosided_disp_transpose.
      }
      apply maponpaths_2.
      apply maponpaths.
      apply idtoiso_twosided_disp_transpose.
    }
    rewrite transportb_disp_mor2_transpose.
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
      apply (runitor_square' (C := C)).
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
  Definition transpose_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact transpose_category.
    - exact transpose_twosided_disp_cat.
    - exact transpose_hor_id.
    - exact transpose_hor_comp.
    - exact transpose_lunitor.
    - exact transpose_runitor.
    - exact transpose_associator.
    - exact transpose_triangle_law.
    - exact transpose_pentagon_law.
  Defined.

  Definition transpose_univalentdouble_cat
             (HC' : is_univalent transpose_category)
             (HC'' : is_univalent_twosided_disp_cat transpose_twosided_disp_cat)
    : univalent_double_cat.
  Proof.
    use make_univalent_double_cat.
    - exact transpose_double_cat.
    - split.
      + exact HC'.
      + exact HC''.
  Defined.
End TransposePseudoDoubleCat.

(** * 11. Symmetric univalence for double categories *)
Definition symmetric_univalent
           (C : univalent_double_cat)
  : UU
  := ∑ (HC : ∏ (x y : C), isaset (x -->h y)),
     is_univalent (transpose_category C HC)
     ×
     is_univalent_twosided_disp_cat (transpose_twosided_disp_cat C HC).

Definition make_symmetric_univalent
           {C : univalent_double_cat}
           (H₁ : ∏ (x y : C), isaset (x -->h y))
           (H₂ : is_univalent (transpose_category C H₁))
           (H₃ : is_univalent_twosided_disp_cat (transpose_twosided_disp_cat C H₁))
  : symmetric_univalent C
  := H₁ ,, H₂ ,, H₃.
