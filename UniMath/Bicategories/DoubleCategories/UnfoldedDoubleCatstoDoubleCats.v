(** * Double Categories

  Authors: Benedikt Ahrens, Paige North, Nima Rasekh, Niels van der Weide
  June 2023
  Based on definition of weak double category in Section 3.3 of the book Higher Dimensional Categories by Marco Grandis.
 *)


(** ** Contents :

  - Define a pre double category as a ``weak double category`` in the sense of Grandis.
    This means one direction is weak and the other direction is strict.

  - Double categories: A double category is a pre-double category with two set-truncated hom sets.
  -
  - Univalent Double Categories: A univalent double category is a double category with two univalent underlying categories.

  - The structure is defined from scratch rather than building on a category.
    This makes further generalizations easier.
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
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
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.DoubleTransformation.
Require Import UniMath.Bicategories.DoubleCategories.BicatOfDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCatsUnfolded.

Local Open Scope cat.
Local Open Scope double_cat.

Definition TODO { A : UU} : A.
Admitted.

Section DoubleCatsUnfolded_to_DoubleCats.
  Context (C : univalent_doublecategory).

  Definition doublecategory_to_cat : category :=
    (und_ob_hor_cat C).

  Definition doublecategory_to_twosided_disp_cat_data
    : twosided_disp_cat_data  (und_ob_hor_cat C) (und_ob_hor_cat C).
  Proof.
    use tpair.
    - use tpair.
      * intros x y.
        exact (x -v-> y).
      * intros x y z w f g h k.
        exact (sqq h f g k).
    - use tpair.
      * intros x y f.
        exact (hor_sq_identity f).
      * intros x y z a b c f1 f2 f3 f4 f5 f6 f7 α β.
        exact (α ·sqh β).
  Defined.

  Definition doublecategory_to_twosided_disp_cat
    : twosided_disp_cat doublecategory_to_cat doublecategory_to_cat.
  Proof.
    use tpair.
    - exact doublecategory_to_twosided_disp_cat_data.
    - repeat split.
      + intros x0 x1 y0 y1 f0 f1 g0 g1 α.
        exact (id_hor_sq_left α).
      + intros x0 x1 y0 y1 f0 f1 g0 g1 α.
        exact (id_hor_sq_right α).
      + intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? α β γ.
        exact (assoc_sq_hor α β γ).
      + intros x0 x1 y0 y1 f0 g0 f1 g1.
        exact (get_has_sq_hor_homsets f0 g0 f1 g1).
  Defined.

  Let D : twosided_disp_cat doublecategory_to_cat doublecategory_to_cat
      := doublecategory_to_twosided_disp_cat.

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
  Admitted.

  Let HD : is_univalent_twosided_disp_cat D
      := is_univalent_doublecategory_to_twosided_disp_cat.

  Definition  doublecategory_to_double_cat : double_cat :=
    make_double_cat (und_ob_hor_cat C) D I Cm l r a tr pe HC HD.
End DoubleCatsUnfolded_to_DoubleCats.

Section DoubleCats_to_DoubleCatsUnfolded.
  Context (C : double_cat).

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
    - exact (λ x y, x -->h y).
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
    - exact (λ x, identity_h x).
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
    - exact (λ w x y z v₁ h₁ h₂ v₂, square v₁ v₂ h₁ h₂).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_id_comp
    : predoublecategory_sq_hor_id_comp double_cat_to_predoublecategory_ob_mor_sq_data.
  Proof.
    split.
    - exact (λ x y f, id_v_square f).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆v s₂).
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
      apply square_id_left_v.
    - intro ; intros ; cbn.
      apply square_id_right_v.
    - intro ; intros ; cbn.
      apply square_assoc_v.
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
    - exact (λ x y f, id_h_square f).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆h s₂).
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
    repeat split ; cbn.
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
    exact (lunitor_square α).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_right_unitor_naturality
    : predoublecategory_ver_right_unitor_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros w x y z v₁ h₁ h₂ v₂ α.
    exact (runitor_square α).
  Defined.

  Proposition double_cat_to_predoublecategory_ver_assoc_naturality
    : predoublecategory_ver_assoc_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros ; cbn.
    apply lassociator_h_square.
  Defined.

  Proposition double_cat_to_predoublecategory_ver_unitor_coherence
    : predoublecategory_ver_unitor_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros ; cbn.
    apply double_triangle.
  Defined.

  Proposition double_cat_to_predoublecategory_ver_assoc_coherence
    : predoublecategory_ver_assoc_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intro ; intros ; cbn.
    apply double_pentagon.
  Defined.

  Proposition double_cat_to_predoublecategory_interchange
    : predoublecategory_interchange
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply id_h_square_id.
    - apply id_h_square_comp.
    - apply comp_h_square_id.
    - apply comp_h_square_comp.
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
    - apply TODO.
  Defined.
End DoubleCats_to_DoubleCatsUnfolded.

Proposition double_cat_weq_univalent_doublecategory_inv₁
            (C : double_cat)
  : doublecategory_to_double_cat (double_cat_to_univalent_doublecategory C) = C.
Proof.
  induction C as [ C1 H ].
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; repeat (use impred ; intro) ; apply isaset_disp_mor.
  }
  induction C1 as [ [ [ C D ] IC ] UnAs ].
  use total2_paths_f.
  - use total2_paths_f.
    + use total2_paths_f.
      * apply idpath.
      * use subtypePath.
        {
          intro.
          apply isaprop_is_univalent_twosided_disp_cat.
        }
        apply idpath.
    + (* rewrite transportf_total2_paths_f. *)
      admit.
  - admit.
Admitted.

Proposition double_cat_weq_univalent_doublecategory_inv₂
            (C : univalent_doublecategory)
  : double_cat_to_univalent_doublecategory (doublecategory_to_double_cat C) = C.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropdirprod.
    - apply isaprop_is_univalent.
    - admit.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod ;
    repeat (use impred ; intro) ;
    apply isapropiscontr.
  }
  induction C as [ [ [ C1 C2 ] C3 ] H ] ; cbn.
  refine (maponpaths (λ z, _ ,, z) _).
  repeat (use pathsdirprod) ;
  repeat (use funextsec ; intro) ;
  apply get_has_sq_hor_homsets.
Admitted.

Definition double_cat_weq_univalent_doublecategory
  : double_cat ≃ univalent_doublecategory.
Proof.
  use weq_iso.
  - exact double_cat_to_univalent_doublecategory.
  - exact doublecategory_to_double_cat.
  - exact double_cat_weq_univalent_doublecategory_inv₁.
  - intros C.
    revert C.
