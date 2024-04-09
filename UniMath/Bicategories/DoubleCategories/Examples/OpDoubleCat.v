(************************************************************************************

 The opposite of double categories

 Every double category gives rise to multiple opposite double categories. The first
 one is given by the vertical opposite. Here we reverse the vertical morphisms. The
 second one is given by the horizontal opposite where we reverse the horizontal
 morphisms. In this file we construct these double categories.

 One technical aspect to note about the construction: at several points, we need to
 prove a coherence, like the triangle law or pentagon law. See, for instance,
 [ver_opposite_double_cat_triangle]. To do so, we use the underlying horizontal
 bicategory and we reuse that certain coherences already hold for bicategories. This
 allows us to deduce them for double categories as well.

 Contents
 1. Vertical opposites of double categories
 1.1. Horizontal identity in the vertical opposite
 1.2. Horizontal composition in the vertical opposite
 1.3. Unitors and associators
 1.4. Triangle and pentagon
 1.5. The vertical opposite
 2. Horizontal opposites of double categories
 2.1. Horizontal identity in the horizontal opposite
 2.2. Horizontal composition in the horizontal opposite
 2.3. Unitors and associators
 2.4. Triangle and pentagon
 2.5. The horizontal opposite

 ************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Opposites.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.Variations.
Require Import UniMath.Bicategories.DoubleCategories.Underlying.HorizontalBicategory.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Vertical opposites of double categories *)
Section VerOpposite.
  Context (C : double_cat).

  (** * 1.1. Horizontal identity in the vertical opposite *)
  Definition hor_id_ver_opposite_double_cat_data
    : hor_id_data (ver_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_id_data.
    - exact (λ (x : C), identity_h x).
    - exact (λ (x y : C) (f : y -->v x), id_h_square f).
  Defined.

  Proposition hor_id_ver_opposite_double_cat_laws
    : hor_id_laws hor_id_ver_opposite_double_cat_data.
  Proof.
    split ; cbn.
    - intro.
      apply id_h_square_id.
    - intros.
      apply id_h_square_comp.
  Qed.

  Definition hor_id_ver_opposite_double_cat
    : hor_id (ver_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_id.
    - exact hor_id_ver_opposite_double_cat_data.
    - exact hor_id_ver_opposite_double_cat_laws.
  Defined.

  (** * 1.2. Horizontal composition in the vertical opposite *)
  Definition hor_comp_ver_opposite_double_cat_data
    : hor_comp_data (ver_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_comp_data.
    - exact (λ (x y z : C) (h : x -->h y) (k : y -->h z), h ·h k).
    - exact (λ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
               (v₁ : x₂ -->v x₁)
               (v₂ : y₂ -->v y₁)
               (v₃ : z₂ -->v z₁)
               (h₁ : x₁ -->h y₁)
               (h₂ : y₁ -->h z₁)
               (k₁ : x₂ -->h y₂)
               (k₂ : y₂ -->h z₂)
               (s₁ : square v₁ v₂ k₁ h₁)
               (s₂ : square v₂ v₃ k₂ h₂),
             s₁ ⋆h s₂).
  Defined.

  Proposition hor_comp_ver_opposite_double_cat_laws
    : hor_comp_laws hor_comp_ver_opposite_double_cat_data.
  Proof.
    split ; cbn.
    - intros.
      apply comp_h_square_id.
    - intros.
      apply comp_h_square_comp.
  Qed.

  Definition hor_comp_ver_opposite_double_cat
    : hor_comp (ver_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_comp.
    - exact hor_comp_ver_opposite_double_cat_data.
    - exact hor_comp_ver_opposite_double_cat_laws.
  Defined.

  (** * 1.3. Unitors and associators *)
  Definition ver_opposite_double_cat_lunitor_data
    : double_lunitor_data
        hor_id_ver_opposite_double_cat
        hor_comp_ver_opposite_double_cat.
  Proof.
    refine (λ (x y : C) (h : x -->h y), _).
    simple refine (_ ,, _).
    - exact (linvunitor_h h).
    - use to_iso_ver_op_twosided_disp_cat.
      refine (lunitor_h h ,, _ ,, _).
      + abstract
          (apply linvunitor_lunitor_h).
      + abstract
          (apply lunitor_linvunitor_h).
  Defined.

  Proposition ver_opposite_double_cat_lunitor_laws
    : double_lunitor_laws ver_opposite_double_cat_lunitor_data.
  Proof.
    intro ; intros.
    cbn.
    refine (_ @ !(linvunitor_square _)).
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition ver_opposite_double_cat_lunitor
    : double_cat_lunitor
        hor_id_ver_opposite_double_cat
        hor_comp_ver_opposite_double_cat.
  Proof.
    use make_double_lunitor.
    - exact ver_opposite_double_cat_lunitor_data.
    - exact ver_opposite_double_cat_lunitor_laws.
  Defined.

  Definition ver_opposite_double_cat_runitor_data
    : double_runitor_data
        hor_id_ver_opposite_double_cat
        hor_comp_ver_opposite_double_cat.
  Proof.
    refine (λ (x y : C) (h : x -->h y), _).
    simple refine (_ ,, _).
    - exact (rinvunitor_h h).
    - use to_iso_ver_op_twosided_disp_cat.
      refine (runitor_h h ,, _ ,, _).
      + abstract
          (apply rinvunitor_runitor_h).
      + abstract
          (apply runitor_rinvunitor_h).
  Defined.

  Proposition ver_opposite_double_cat_runitor_laws
    : double_runitor_laws ver_opposite_double_cat_runitor_data.
  Proof.
    intro ; intros.
    cbn.
    refine (_ @ !(rinvunitor_square _)).
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition ver_opposite_double_cat_runitor
    : double_cat_runitor
        hor_id_ver_opposite_double_cat
        hor_comp_ver_opposite_double_cat.
  Proof.
    use make_double_runitor.
    - exact ver_opposite_double_cat_runitor_data.
    - exact ver_opposite_double_cat_runitor_laws.
  Defined.

  Definition ver_opposite_double_cat_associator_data
    : double_associator_data
        hor_comp_ver_opposite_double_cat.
  Proof.
    refine (λ (w x y z : C) (h₁ : w -->h x) (h₂ : x -->h y) (h₃ : y -->h z), _).
    simple refine (_ ,, _).
    - exact (rassociator_h h₁ h₂ h₃).
    - use to_iso_ver_op_twosided_disp_cat.
      refine (lassociator_h h₁ h₂ h₃ ,, _ ,, _).
      + abstract
          (apply rassociator_lassociator_h).
      + abstract
          (apply lassociator_rassociator_h).
  Defined.

  Proposition ver_opposite_double_cat_associator_laws
    : double_associator_laws ver_opposite_double_cat_associator_data.
  Proof.
    intro ; intros.
    cbn in *.
    refine (_ @ !(rassociator_square _ _ _)).
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition ver_opposite_double_cat_associator
    : double_cat_associator
        hor_comp_ver_opposite_double_cat.
  Proof.
    use make_double_associator.
    - exact ver_opposite_double_cat_associator_data.
    - exact ver_opposite_double_cat_associator_laws.
  Defined.

  (** * 1.4. Triangle and pentagon *)
  Proposition ver_opposite_double_cat_triangle
    : triangle_law
        ver_opposite_double_cat_lunitor
        ver_opposite_double_cat_runitor
        ver_opposite_double_cat_associator.
  Proof.
    intros x y z h k ; cbn.
    pose (triangle_r_inv (C := horizontal_bicat C) k h) as p.
    cbn in p.
    rewrite !comp_h_square_id in p.
    rewrite square_id_left_v in p.
    rewrite square_id_right_v in p.
    unfold transportb_square in p.
    rewrite transportf_f_square in p.
    refine (!_).
    refine (_ @ maponpaths (transportb_square (id_v_left _) (id_v_left _)) p @ _).
    - unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - unfold transportb_square.
      rewrite !transportf_square_prewhisker.
      rewrite !transportf_f_square.
      apply transportf_square_id.
  Qed.

  Proposition ver_opposite_double_cat_pentagon
    : pentagon_law ver_opposite_double_cat_associator.
  Proof.
    intros v w x y z h₁ h₂ h₃ h₄ ; cbn.
    pose (rassociator_rassociator (C := horizontal_bicat C) h₁ h₂ h₃ h₄) as p.
    cbn in p.
    refine (_
            @ maponpaths
                (transportb_square
                   (id_v_left _ @ id_v_left _)
                   (id_v_left _ @ id_v_left _))
                (!p)
            @ _).
    - unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite !transportf_f_square.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply square_assoc_v'.
      }
      rewrite transportf_f_square.
      apply transportf_square_id.
  Qed.

  (** * 1.5. The vertical opposite *)
  Definition ver_opposite_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact (C^op).
    - exact (ver_op_twosided_disp_cat (hor_mor C)).
    - exact hor_id_ver_opposite_double_cat.
    - exact hor_comp_ver_opposite_double_cat.
    - exact ver_opposite_double_cat_lunitor.
    - exact ver_opposite_double_cat_runitor.
    - exact ver_opposite_double_cat_associator.
    - exact ver_opposite_double_cat_triangle.
    - exact ver_opposite_double_cat_pentagon.
  Defined.
End VerOpposite.

Definition ver_opposite_univalent_double_cat
           (C : univalent_double_cat)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (ver_opposite_double_cat C).
  - split.
    + apply op_is_univalent.
    + apply is_univalent_ver_op_twosided_disp_cat.
      apply is_univalent_twosided_disp_cat_hor_mor.
Defined.

Definition ver_opposite_pseudo_double_set_cat
           (C : pseudo_double_setcat)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (ver_opposite_double_cat C).
  - apply opp_setcategory.
  - apply is_strict_ver_op_twosided_disp_cat.
    apply is_strict_twosided_disp_cat_hor_mor.
Defined.

(** * 2. Horizontal opposites of double categories *)
Section HorOpposite.
  Context (C : double_cat).

  (** * 2.1. Horizontal identity in the horizontal opposite *)
  Definition hor_id_hor_opposite_double_cat_data
    : hor_id_data (hor_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_id_data.
    - exact (λ (x : C), identity_h x).
    - exact (λ (x y : C) (f : x -->v y), id_h_square f).
  Defined.

  Proposition hor_id_hor_opposite_double_cat_laws
    : hor_id_laws hor_id_hor_opposite_double_cat_data.
  Proof.
    split ; cbn.
    - intro.
      apply id_h_square_id.
    - intros.
      apply id_h_square_comp.
  Qed.

  Definition hor_id_hor_opposite_double_cat
    : hor_id (hor_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_id.
    - exact hor_id_hor_opposite_double_cat_data.
    - exact hor_id_hor_opposite_double_cat_laws.
  Defined.

  (** * 2.2. Horizontal composition in the horizontal opposite *)
  Definition hor_comp_hor_opposite_double_cat_data
    : hor_comp_data (hor_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_comp_data.
    - exact (λ (x y z : C) (h : y -->h x) (k : z -->h y), k ·h h).
    - exact (λ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
               (v₁ : x₁ -->v x₂)
               (v₂ : y₁ -->v y₂)
               (v₃ : z₁ -->v z₂)
               (h₁ : y₁ -->h x₁)
               (h₂ : z₁ -->h y₁)
               (k₁ : y₂ -->h x₂)
               (k₂ : z₂ -->h y₂)
               (s₁ : square v₂ v₁ h₁ k₁)
               (s₂ : square v₃ v₂ h₂ k₂),
             s₂ ⋆h s₁).
  Defined.

  Proposition hor_comp_hor_opposite_double_cat_laws
    : hor_comp_laws hor_comp_hor_opposite_double_cat_data.
  Proof.
    split ; cbn.
    - intros.
      apply comp_h_square_id.
    - intros.
      apply comp_h_square_comp.
  Qed.

  Definition hor_comp_hor_opposite_double_cat
    : hor_comp (hor_op_twosided_disp_cat (hor_mor C)).
  Proof.
    use make_hor_comp.
    - exact hor_comp_hor_opposite_double_cat_data.
    - exact hor_comp_hor_opposite_double_cat_laws.
  Defined.

  (** * 2.3. Unitors and associators *)
  Definition hor_opposite_double_cat_lunitor_data
    : double_lunitor_data
        hor_id_hor_opposite_double_cat
        hor_comp_hor_opposite_double_cat.
  Proof.
    refine (λ (x y : C) (h : y -->h x), _).
    simple refine (_ ,, _).
    - exact (runitor_h h).
    - use to_iso_hor_op_twosided_disp_cat.
      refine (rinvunitor_h h ,, _ ,, _).
      + abstract
          (apply runitor_rinvunitor_h).
      + abstract
          (apply rinvunitor_runitor_h).
  Defined.

  Proposition hor_opposite_double_cat_lunitor_laws
    : double_lunitor_laws hor_opposite_double_cat_lunitor_data.
  Proof.
    intro ; intros.
    cbn.
    refine (_ @ !(runitor_square _)).
    rewrite transportb_disp_mor2_hor_op.
    use transportb_square_eq.
    apply idpath.
  Qed.

  Definition hor_opposite_double_cat_lunitor
    : double_cat_lunitor
        hor_id_hor_opposite_double_cat
        hor_comp_hor_opposite_double_cat.
  Proof.
    use make_double_lunitor.
    - exact hor_opposite_double_cat_lunitor_data.
    - exact hor_opposite_double_cat_lunitor_laws.
  Defined.

  Definition hor_opposite_double_cat_runitor_data
    : double_runitor_data
        hor_id_hor_opposite_double_cat
        hor_comp_hor_opposite_double_cat.
  Proof.
    refine (λ (x y : C) (h : y -->h x), _).
    simple refine (_ ,, _).
    - exact (lunitor_h h).
    - use to_iso_hor_op_twosided_disp_cat.
      refine (linvunitor_h h ,, _ ,, _).
      + abstract
          (apply lunitor_linvunitor_h).
      + abstract
          (apply linvunitor_lunitor_h).
  Defined.

  Proposition hor_opposite_double_cat_runitor_laws
    : double_runitor_laws hor_opposite_double_cat_runitor_data.
  Proof.
    intro ; intros.
    cbn.
    refine (_ @ !(lunitor_square _)).
    rewrite transportb_disp_mor2_hor_op.
    use transportb_square_eq.
    apply idpath.
  Qed.

  Definition hor_opposite_double_cat_runitor
    : double_cat_runitor
        hor_id_hor_opposite_double_cat
        hor_comp_hor_opposite_double_cat.
  Proof.
    use make_double_runitor.
    - exact hor_opposite_double_cat_runitor_data.
    - exact hor_opposite_double_cat_runitor_laws.
  Defined.

  Definition hor_opposite_double_cat_associator_data
    : double_associator_data
        hor_comp_hor_opposite_double_cat.
  Proof.
    refine (λ (w x y z : C) (h₁ : x -->h w) (h₂ : y -->h x) (h₃ : z -->h y), _).
    simple refine (_ ,, _).
    - exact (rassociator_h h₃ h₂ h₁).
    - use to_iso_hor_op_twosided_disp_cat.
      refine (lassociator_h h₃ h₂ h₁ ,, _ ,, _).
      + abstract
          (apply rassociator_lassociator_h).
      + abstract
          (apply lassociator_rassociator_h).
  Defined.

  Proposition hor_opposite_double_cat_associator_laws
    : double_associator_laws hor_opposite_double_cat_associator_data.
  Proof.
    intro ; intros.
    cbn in *.
    refine (_ @ rassociator_square' _ _ _).
    rewrite transportb_disp_mor2_hor_op.
    use transportb_square_eq.
    apply idpath.
  Qed.

  Definition hor_opposite_double_cat_associator
    : double_cat_associator
        hor_comp_hor_opposite_double_cat.
  Proof.
    use make_double_associator.
    - exact hor_opposite_double_cat_associator_data.
    - exact hor_opposite_double_cat_associator_laws.
  Defined.

  (** * 2.4. Triangle and pentagon *)
  Proposition hor_opposite_double_cat_triangle
    : triangle_law
        hor_opposite_double_cat_lunitor
        hor_opposite_double_cat_runitor
        hor_opposite_double_cat_associator.
  Proof.
    intros x y z h k ; cbn.
    pose (triangle_l (C := horizontal_bicat C) h k) as p.
    cbn in p.
    rewrite !comp_h_square_id in p.
    rewrite square_id_left_v in p.
    rewrite square_id_right_v in p.
    unfold transportb_square in p.
    rewrite !transportf_square_postwhisker in p.
    rewrite !transportf_f_square in p.
    refine (_ @ maponpaths (transportb_square (id_v_left _) (id_v_left _)) p @ _).
    - unfold transportb_square.
      rewrite transportf_f_square.
      refine (!_).
      apply transportf_square_id.
    - unfold transportb_square.
      rewrite !transportf_f_square.
      rewrite transportb_disp_mor2_hor_op.
      use transportf_disp_mor2_eq.
      apply idpath.
  Qed.

  Proposition hor_opposite_double_cat_pentagon
    : pentagon_law hor_opposite_double_cat_associator.
  Proof.
    intros v w x y z h₁ h₂ h₃ h₄ ; cbn.
    pose (rassociator_rassociator (C := horizontal_bicat C) h₄ h₃ h₂ h₁) as p.
    cbn in p.
    simple refine (_
            @ maponpaths
                (transportb_square
                   (id_v_right _ @ id_v_right _)
                   (id_v_right _ @ id_v_right _))
                (!p)
            @ _).
    - unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportb_disp_mor2_hor_op.
      use transportf_disp_mor2_eq.
      apply idpath.
    - unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite !transportf_f_square.
      apply transportf_square_id.
  Qed.

  (** * 2.5. The horizontal opposite *)
  Definition hor_opposite_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact C.
    - exact (hor_op_twosided_disp_cat (hor_mor C)).
    - exact hor_id_hor_opposite_double_cat.
    - exact hor_comp_hor_opposite_double_cat.
    - exact hor_opposite_double_cat_lunitor.
    - exact hor_opposite_double_cat_runitor.
    - exact hor_opposite_double_cat_associator.
    - exact hor_opposite_double_cat_triangle.
    - exact hor_opposite_double_cat_pentagon.
  Defined.
End HorOpposite.

Definition hor_opposite_univalent_double_cat
           (C : univalent_double_cat)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (hor_opposite_double_cat C).
  - split.
    + apply univalent_category_is_univalent.
    + apply is_univalent_hor_op_twosided_disp_cat.
      apply is_univalent_twosided_disp_cat_hor_mor.
Defined.

Definition hor_opposite_pseudo_double_set_cat
           (C : pseudo_double_setcat)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (hor_opposite_double_cat C).
  - apply is_setcategory_vertical_cat.
  - apply is_strict_hor_op_twosided_disp_cat.
    apply is_strict_twosided_disp_cat_hor_mor.
Defined.
