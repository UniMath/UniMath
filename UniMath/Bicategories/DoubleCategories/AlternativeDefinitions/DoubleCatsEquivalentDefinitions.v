(** * Double Categories

  Authors: Benedikt Ahrens, Paige North, Nima Rasekh, Niels van der Weide
  June 2023

  We construct an equivalence between the unfolded definition and the folded
  definition of double categories. The proof is a matter of reorganizing the
  sigma type.

  Contents:
  1. The map from unfolded double categories to double categories
  2. The inverse
  3. It forms an equivalences
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.BicatOfDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.AlternativeDefinitions.DoubleCatsUnfolded.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. The map from unfolded double categories to double categories *)
Section DoubleCatsUnfolded_to_DoubleCats.
  Context (C : univalent_doublecategory).

  Definition doublecategory_to_cat : category :=
    (und_ob_hor_cat C).

  Let D : twosided_disp_cat doublecategory_to_cat doublecategory_to_cat
      := doublecategory_to_twosided_disp_cat C.

  Definition doublecategory_to_horid : hor_id D.
  Proof.
    use make_hor_id.
    - use make_hor_id_data.
      + intro x.
        exact (ver_identity x).
      + intros x y f.
        exact (ver_sq_identity f).
    - split.
      + intro x.
        exact (get_predoublecategory_interchange_id_obj x).
      + intros x y z f g.
        exact ( get_predoublecategory_interchange_id_hor f g).
  Defined.

  Let I : hor_id D := doublecategory_to_horid.

  Definition doublecategory_to_horcomp : hor_comp D.
  Proof.
    use make_hor_comp.
    - use make_hor_comp_data.
      + intros x y z f g.
        exact (ver_compose f g).
      + cbn in *.
        intros x1 x2 y1 y2 z1 z2 v1 v2 v3 h1 h2 k1 k2 α β.
        exact (ver_sq_compose α β).
    - split.
      + cbn in *.
        intros x y z f g.
        exact (get_predoublecategory_interchange_id_ver f g).
      + cbn in *.
        intros a0 a1 a2 b0 b1 b2 c0 c1 c2 fa ga fb gb fc gc h0 k0 h1 k1 h2 k2 α β γ δ.
        exact (get_predoublecategory_interchange_comp α β γ δ).
  Defined.

  Let Cm : hor_comp D := doublecategory_to_horcomp.

  Definition  doublecategory_to_lunitor : double_cat_lunitor I Cm.
  Proof.
    use make_double_lunitor.
    - intros x y h.
      use make_iso_twosided_disp.
      + cbn in *.
        exact (pr1 (get_ver_left_unitor h)).
      + simple refine (_ ,, _ ,, _).
        * exact (pr12 (get_ver_left_unitor h)).
        * cbn in *. exact (pr122 (get_ver_left_unitor h)).
        * exact (pr222 (get_ver_left_unitor h)).
    - cbn in *.
      intros a b c d f g h k α.
      exact (! get_predoublecategory_ver_left_unitor_naturality α).
  Defined.

  Let l : double_cat_lunitor I Cm := doublecategory_to_lunitor.

  Definition doublecategory_to_runitor : double_cat_runitor I Cm.
  Proof.
    use make_double_runitor.
    - intros x y h.
      use make_iso_twosided_disp.
      + cbn in *.
        exact (pr1 (get_ver_right_unitor h)).
      + simple refine (_ ,, _ ,, _).
        * exact (pr12 (get_ver_right_unitor h)).
        * cbn in *. exact (pr122 (get_ver_right_unitor h)).
        * exact (pr222 (get_ver_right_unitor h)).
    - cbn in *.
      intros a b c d f g h k α.
      exact (! get_predoublecategory_ver_right_unitor_naturality α).
  Defined.

  Let r : double_cat_runitor I Cm := doublecategory_to_runitor.

  Definition doublecategory_to_associator : double_cat_associator Cm.
  Proof.
    use make_double_associator.
    - intros w x y z f g h.
      use make_iso_twosided_disp.
      + exact (pr1 (get_ver_associator f g h)).
      + simple refine (_ ,, _ ,, _).
        * exact (pr12 (get_ver_associator f g h)).
        * exact (pr122 (get_ver_associator f g h)).
        * exact (pr222 (get_ver_associator f g h)).
    - cbn in *.
      intros a0 a1 a2 a3 b0 b1 b2 b3 fa fb ha hb ka kb g0 g1 g2 g3 α β γ.
      exact (! get_predoublecategory_ver_assoc_naturality α β γ).
  Defined.

  Let a : double_cat_associator Cm := doublecategory_to_associator.

  Proposition doublecategory_to_triangle : triangle_law l r a.
  Proof.
    intros x y z h k.
    cbn in *.
    exact (get_predoublecategory_ver_unitor_coherence h k).
  Defined.

  Let tr : triangle_law l r a := doublecategory_to_triangle.

  Proposition doublecategory_to_pentagon : pentagon_law a.
  Proof.
    intros i b c d e f g h k.
    exact (get_predoublecategory_ver_assoc_coherence f g h k).
  Defined.

  Let pe : pentagon_law a := doublecategory_to_pentagon.

  Definition is_univalent_und_ob_hor_cat : is_univalent (und_ob_hor_cat C).
  Proof.
    apply C.
  Defined.

  Let HC : is_univalent (und_ob_hor_cat C) := is_univalent_und_ob_hor_cat.

  Definition is_univalent_doublecategory_to_twosided_disp_cat
    : is_univalent_twosided_disp_cat D.
  Proof.
    apply C.
  Defined.

  Let HD : is_univalent_twosided_disp_cat D
      := is_univalent_doublecategory_to_twosided_disp_cat.

  Definition  doublecategory_to_double_cat : double_cat :=
    make_double_cat (und_ob_hor_cat C) D I Cm l r a tr pe.

  Definition  doublecategory_to_univalent_double_cat : univalent_double_cat :=
    make_univalent_double_cat doublecategory_to_double_cat (HC ,, HD).
End DoubleCatsUnfolded_to_DoubleCats.

(** * 2. The inverse *)
Section DoubleCats_to_DoubleCatsUnfolded.
  Context (C : univalent_double_cat).

  Definition double_cat_to_predoublecategory_ob_mor_hor
    : predoublecategory_ob_mor_hor.
  Proof.
    simple refine (_ ,, _).
    - exact C.
    - exact (λ x y, x -->v y).
  Defined.

  Definition double_cat_to_predoublecategory_ob_mor_data
    : predoublecategory_ob_mor_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_hor.
    - exact (λ (x y : C), x -->h y).
  Defined.

  Definition double_cat_to_predoublecategory_hor_id_comp
    : predoublecategory_hor_id_comp double_cat_to_predoublecategory_ob_mor_data.
  Proof.
    split.
    - exact (λ x, identity x).
    - exact (λ x y z f g, f · g).
  Defined.

  Definition double_cat_to_predoublecategory_hor_precat_data
    : predoublecategory_hor_precat_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_data.
    - exact double_cat_to_predoublecategory_hor_id_comp.
  Defined.

  Proposition double_cat_to_is_predoublecategory_hor
    : is_predoublecategory_hor double_cat_to_predoublecategory_hor_precat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      apply id_left.
    - intro ; intros ; cbn.
      apply id_right.
    - intro ; intros ; cbn.
      apply assoc.
    - intro ; intros ; cbn.
      apply assoc'.
  Defined.

  Definition double_cat_to_predoublecategory_hor
    : predoublecategory_hor.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_precat_data.
    - exact double_cat_to_is_predoublecategory_hor.
  Defined.

  Definition double_cat_to_predoublecategory_ver_id_comp
    : predoublecategory_ver_id_comp double_cat_to_predoublecategory_hor.
  Proof.
    split.
    - exact (λ x, identity_h (C := C) x).
    - exact (λ x y z f g, f ·h g).
  Defined.

  Definition double_cat_to_predoublecategory_hor_cat_ver_precat_data
    : predoublecategory_hor_cat_ver_precat_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor.
    - exact double_cat_to_predoublecategory_ver_id_comp.
  Defined.

  Definition double_cat_to_predoublecategory_ob_mor_sq_data
    : predoublecategory_ob_mor_sq_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_cat_ver_precat_data.
    - exact (λ w x y z v₁ h₁ h₂ v₂, square (C := C) v₁ v₂ h₁ h₂).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_id_comp
    : predoublecategory_sq_hor_id_comp double_cat_to_predoublecategory_ob_mor_sq_data.
  Proof.
    split.
    - exact (λ x y f, id_v_square f).
    - exact (λ (_ _ : C) _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆v s₂).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_data
    : predoublecategory_sq_hor_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_sq_data.
    - exact double_cat_to_predoublecategory_sq_hor_id_comp.
  Defined.

  Proposition double_cat_to_is_predoublecategory_hor_sq
    : is_predoublecategory_hor_sq double_cat_to_predoublecategory_sq_hor_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      apply (square_id_left_v (C := C)).
    - intro ; intros ; cbn.
      apply (square_id_right_v (C := C)).
    - intro ; intros ; cbn.
      apply (square_assoc_v (C := C)).
  Defined.

  Definition double_cat_to_predoublecategory_hor_sq
    : predoublecategory_hor_sq.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_data.
    - exact double_cat_to_is_predoublecategory_hor_sq.
  Defined.

  Definition double_cat_to_predoublecategory_sq_ver_id_comp
    : predoublecategory_sq_ver_id_comp double_cat_to_predoublecategory_hor_sq.
  Proof.
    split.
    - exact (λ x y f, id_h_square (C := C) f).
    - exact (λ (_ _ : C) _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆h s₂).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_ver_data
    : predoublecategory_sq_hor_ver_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_sq.
    - exact double_cat_to_predoublecategory_sq_ver_id_comp.
  Defined.

  Proposition double_cat_to_has_predoublecategory_sq_hor_ver_unit_assoc
    : has_predoublecategory_sq_hor_ver_unit_assoc
        double_cat_to_predoublecategory_sq_hor_ver_data.
  Proof.
    repeat split.
    - intros x y f.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + exact (lunitor_h f).
      + exact (linvunitor_h f).
      + exact (lunitor_linvunitor_h f).
      + exact (linvunitor_lunitor_h f).
    - intros x y f.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + exact (runitor_h f).
      + exact (rinvunitor_h f).
      + exact (runitor_rinvunitor_h f).
      + exact (rinvunitor_runitor_h f).
    - intros w x y z f g h.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + exact (lassociator_h f g h).
      + exact (rassociator_h f g h).
      + exact (lassociator_rassociator_h f g h).
      + exact (rassociator_lassociator_h f g h).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data
    : predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_ver_data.
    - exact double_cat_to_has_predoublecategory_sq_hor_ver_unit_assoc.
  Defined.

  Proposition double_cat_to_predoublecategory_ver_left_unitor_naturality
    : predoublecategory_ver_left_unitor_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros w x y z v₁ h₁ h₂ v₂ α.
    exact (lunitor_square (C := C) α).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_right_unitor_naturality
    : predoublecategory_ver_right_unitor_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros w x y z v₁ h₁ h₂ v₂ α.
    exact (runitor_square (C := C) α).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_assoc_naturality
    : predoublecategory_ver_assoc_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros.
    apply (lassociator_square (C := C)).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_unitor_coherence
    : predoublecategory_ver_unitor_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros ; cbn.
    apply (double_triangle (C := C)).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_assoc_coherence
    : predoublecategory_ver_assoc_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros ; cbn.
    apply (double_pentagon (C := C)).
  Defined.

  Proposition double_cat_to_predoublecategory_interchange
    : predoublecategory_interchange
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply (id_h_square_id (C := C)).
    - apply (id_h_square_comp (C := C)).
    - apply (comp_h_square_id (C := C)).
    - apply (comp_h_square_comp (C := C)).
  Defined.

  Definition double_cat_to_predoublecategory
    : predoublecategory.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
    - exact double_cat_to_predoublecategory_ver_left_unitor_naturality.
    - exact double_cat_to_predoublecategory_ver_right_unitor_naturality.
    - exact double_cat_to_predoublecategory_ver_assoc_naturality.
    - exact double_cat_to_predoublecategory_ver_unitor_coherence.
    - exact double_cat_to_predoublecategory_ver_assoc_coherence.
    - exact double_cat_to_predoublecategory_interchange.
  Defined.

  Definition double_cat_to_doublecategory
    : doublecategory.
  Proof.
    use make_doublecategory.
    - exact double_cat_to_predoublecategory.
    - apply homset_property.
    - intro ; intros ; cbn.
      apply isaset_disp_mor.
  Defined.

  Definition double_cat_to_univalent_doublecategory
    : univalent_doublecategory.
  Proof.
    simple refine (double_cat_to_doublecategory ,, _ ,, _).
    - exact (pr21 (pr111 C)).
    - exact (pr22 (pr111 C)).
  Defined.
End DoubleCats_to_DoubleCatsUnfolded.

(** * 3. It forms an equivalence *)
Proposition double_cat_weq_univalent_doublecategory_inv₁
            (C : univalent_double_cat)
  : doublecategory_to_univalent_double_cat (double_cat_to_univalent_doublecategory C) = C.
Proof.
  induction C as [ C1 H ].
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; repeat (use impred ; intro) ; apply isaset_disp_mor.
  }
  use total2_paths_f ; [ apply idpath | ].
  use pathsdirprod.
  - use subtypePath.
    {
      intro.
      apply isaprop_double_lunitor_laws.
    }
    apply idpath.
  - use pathsdirprod.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_runitor_laws.
      }
      apply idpath.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_associator_laws.
      }
      apply idpath.
Qed.

Proposition double_cat_weq_univalent_doublecategory_inv₂
            (C : univalent_doublecategory)
  : double_cat_to_univalent_doublecategory (doublecategory_to_univalent_double_cat C) = C.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropdirprod.
    - apply isaprop_is_univalent.
    - apply isaprop_is_univalent_twosided_disp_cat.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod ;
    repeat (use impred ; intro) ;
    apply isapropiscontr.
  }
  use total2_paths_f ; [ apply idpath | ].
  repeat (use pathsdirprod) ;
  repeat (use funextsec ; intro) ;
  apply get_has_sq_hor_homsets.
Qed.

Definition univalent_double_cat_weq_univalent_doublecategory
  : univalent_double_cat ≃ univalent_doublecategory.
Proof.
  use weq_iso.
  - exact double_cat_to_univalent_doublecategory.
  - exact doublecategory_to_univalent_double_cat.
  - exact double_cat_weq_univalent_doublecategory_inv₁.
  - exact double_cat_weq_univalent_doublecategory_inv₂.
Defined.
