(********************************************************************************

 Horizontal bicategory of a pseudo double category

 Every pseudo double category `C` gives rise to a horizontal bicategory defined as
 follows:
 - Objects: objects of `C`
 - 1-cells: horizontal morphisms of `C`
 - 2-cells: globular squares
 Composition of 2-cells is given as follows

<<
 x --|--> y
 |        |
 |        |
 V        V
 x --|--> y
 |        |
 |        |
 V        V
 x --|--> y
>>

 This is a globular square, because both vertical sides are equal to the identity
 since unitality of vertical morphisms is strict.

 We also show that this bicategory is univalent if our pseudo double category is
 univalent. The idea behind this proof is that equality of horizontal morphisms
 is the same as globular isomorphism squares, because we assume the horizontal
 categories of `C` to be univalent. Invertible 2-cells in the horizontal
 bicategory are the same as globular isomorphism squares.

 Content
 1. The data of the horizontal bicategory
 2. The laws of the horizontal bicategory
 3. The horizontal bicategory
 4. Local univalence of the bicategory

 ********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.
Import TransportSquare.

Local Open Scope cat.
Local Open Scope double_cat.

Section HorizontalBicat.
  Context (C : double_cat).

  (** * 1. The data of the horizontal bicategory *)
  Definition horizontal_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact C.
    - exact (λ x y, x -->h y).
  Defined.

  Definition horizontal_precategory_id_comp
    : precategory_id_comp horizontal_precategory_ob_mor.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ x, identity_h x).
    - exact (λ _ _ _ f g, f ·h g).
  Defined.

  Definition horizontal_precategory_data
    : precategory_data.
  Proof.
    simple refine (_ ,, _).
    - exact horizontal_precategory_ob_mor.
    - exact horizontal_precategory_id_comp.
  Defined.

  Definition horizontal_prebicat_1_id_comp_cells
    : prebicat_1_id_comp_cells.
  Proof.
    simple refine (_ ,, _).
    - exact horizontal_precategory_data.
    - intros x y f g ; cbn in x, y, f, g.
      exact (square (identity_v x) (identity_v y) f g).
  Defined.

  Definition horizontal_prebicat_2_id_comp_struct
    : prebicat_2_id_comp_struct horizontal_prebicat_1_id_comp_cells.
  Proof.
    repeat split ; cbn.
    - exact (λ x y f, id_v_square f).
    - exact (λ x y f, lunitor_h f).
    - exact (λ x y f, runitor_h f).
    - exact (λ x y f, linvunitor_h f).
    - exact (λ x y f, rinvunitor_h f).
    - exact (λ w x y z f g h, rassociator_h f g h).
    - exact (λ w x y z f g h, lassociator_h f g h).
    - exact (λ x y f g h s₁ s₂,
             transportf_square
               (id_v_left _) (id_v_left _)
               (s₁ ⋆v s₂)).
    - exact (λ x y z f g₁ g₂ s, id_v_square f ⋆h s).
    - exact (λ x y z f₁ f₂ g s, s ⋆h id_v_square g).
  Defined.

  Definition horizontal_prebicat_data
    : prebicat_data.
  Proof.
    use make_prebicat_data.
    - exact horizontal_prebicat_1_id_comp_cells.
    - exact horizontal_prebicat_2_id_comp_struct.
  Defined.

  (** * 2. The laws of the horizontal bicategory *)
  Proposition horizontal_prebicat_laws
    : prebicat_laws horizontal_prebicat_data.
  Proof.
    repeat split ; cbn.
    - intros x y f g s.
      rewrite square_id_left_v.
      rewrite transportfb_square.
      apply idpath.
    - intros x y f g s.
      rewrite square_id_right_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      apply transportf_square_id.
    - intros x y f g h k s₁ s₂ s₃.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      rewrite !transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y z f g.
      rewrite comp_h_square_id.
      apply idpath.
    - intros x y z f g.
      rewrite comp_h_square_id.
      apply idpath.
    - intros x y z f g h i s₁ s₂.
      rewrite <- comp_h_square_comp.
      rewrite square_id_left_v.
      unfold transportb_square.
      rewrite transportf_hcomp_r.
      rewrite transportf_hcomp_l.
      rewrite transportf_f_square.
      use transportf_square_eq.
      rewrite transportf_hcomp_l.
      rewrite transportf_square_id.
      apply idpath.
    - intros x y z f g h i s₁ s₂.
      rewrite <- comp_h_square_comp.
      rewrite square_id_left_v.
      unfold transportb_square.
      rewrite transportf_hcomp_l.
      rewrite transportf_hcomp_r.
      rewrite transportf_f_square.
      use transportf_square_eq.
      rewrite transportf_hcomp_l.
      rewrite transportf_square_id.
      apply maponpaths.
      use transportf_square_eq.
      apply idpath.
    - intros x y f g s.
      rewrite <- id_h_square_id.
      rewrite (lunitor_square s).
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y f g s.
      rewrite <- id_h_square_id.
      rewrite (runitor_square s).
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z f g h i s.
      rewrite lassociator_square.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite <- comp_h_square_id.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z f g h i s.
      rewrite lassociator_square.
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z f g h i s.
      rewrite <- comp_h_square_id.
      rewrite lassociator_square.
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y z f g h i s₁ s₂.
      rewrite <- !comp_h_square_comp.
      rewrite !square_id_left_v.
      rewrite !square_id_right_v.
      unfold transportb_square.
      use transportf_square_eq.
      use eq_hcomp_square.
      + apply idpath.
      + rewrite transportf_square_id.
        use transportf_square_eq.
        apply idpath.
      + rewrite transportf_square_id.
        use transportf_square_eq.
        apply idpath.
    - intros x y f.
      rewrite lunitor_linvunitor_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros x y f.
      rewrite linvunitor_lunitor_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros x y f.
      rewrite runitor_rinvunitor_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros x y f.
      rewrite rinvunitor_runitor_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros w x y z f g h.
      rewrite lassociator_rassociator_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros w x y z f g h.
      rewrite rassociator_lassociator_h.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros x y z f g.
      rewrite double_triangle.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_square_id.
      apply idpath.
    - intros v w x y z f g h i.
      rewrite double_pentagon'.
      rewrite transportf_square_prewhisker.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
  Qed.

  Definition horizontal_prebicat
    : prebicat.
  Proof.
    simple refine (_ ,, _).
    - exact horizontal_prebicat_data.
    - exact horizontal_prebicat_laws.
  Defined.

  (** * 3. The horizontal bicategory *)
  Definition horizontal_bicat
    : bicat.
  Proof.
    refine (horizontal_prebicat ,, _).
    intros x y f g.
    apply isaset_square.
  Defined.

  (** * 4. Local univalence of the bicategory *)
  Definition is_invertible_2cell_weq_is_iso_twosided_disp
             {x y : C}
             {h k : x -->h y}
             (s : square (identity_v x) (identity_v y) h k)
    : is_iso_twosided_disp (identity_is_z_iso x) (identity_is_z_iso y) s
      ≃
      is_invertible_2cell (C := horizontal_bicat) s.
  Proof.
    use weqimplimpl.
    - intros Hs.
      use make_is_invertible_2cell.
      + exact (iso_inv_twosided_disp Hs).
      + cbn.
        etrans.
        {
          apply maponpaths.
          exact (inv_after_iso_twosided_disp Hs).
        }
        apply transportfb_square.
      + cbn.
        etrans.
        {
          apply maponpaths.
          exact (iso_after_inv_twosided_disp Hs).
        }
        apply transportfb_square.
    - intros Hs.
      simple refine (_ ,, _ ,, _).
      + exact (Hs^-1).
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(vcomp_rinv Hs)).
        }
        apply transportbf_square.
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(vcomp_linv Hs)).
        }
        apply transportbf_square.
    - apply isaprop_is_iso_twosided_disp.
    - apply isaprop_is_invertible_2cell.
  Qed.
End HorizontalBicat.

Definition is_univalent_2_1_horizontal_bicat
           (C : univalent_double_cat)
  : is_univalent_2_1 (horizontal_bicat C).
Proof.
  intros x y h k.
  use weqhomot.
  - refine (weqfibtototal _ _ _ ∘ path_weq_globular_iso_square h k)%weq.
    exact (is_invertible_2cell_weq_is_iso_twosided_disp C).
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    cbn.
    rewrite path_to_globular_iso_square_id.
    apply idpath.
Qed.

Definition locally_strict_horizontal_bicat
           (C : pseudo_double_setcat)
  : locally_strict (horizontal_bicat C).
Proof.
  intros x y.
  apply is_strict_twosided_disp_cat_hor_mor.
Qed.

Definition globally_strict_horizontal_bicat
           (C : pseudo_double_setcat)
  : globally_strict (horizontal_bicat C).
Proof.
  apply is_setcategory_vertical_cat.
Qed.

Definition horizontal_bisetcat
          (C : pseudo_double_setcat)
  : bisetcat.
Proof.
  refine (horizontal_bicat C ,, _).
  split.
  - apply locally_strict_horizontal_bicat.
  - apply globally_strict_horizontal_bicat.
Defined.
