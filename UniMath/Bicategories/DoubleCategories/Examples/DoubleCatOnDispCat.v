(*******************************************************************************************

 Displayed categories on vertical categories

 We discuss a way to construct more complicated double categories from simpler ones. More
 specifically, suppose that we have a pseudo double category `C` and a displayed category `D`
 on the vertical category of `C`. Then we have a double category whose vertical category is
 given by the total category of `D`. This construction is useful for several reasons and one
 of them is that it allows us to construct full subdouble categories.

 If we look at this construction from a broader perspective, then this construction would be
 a special case of 'displayed double categories'. Intuitively, we can add structure/properties
 to the objects, morphisms, and squares of a double category in two step. First, we add
 structure/properties to the objects and vertical morphisms. This is described by a displayed
 category over the vertical category, and the corresponding construction is given in this file.
 The second step would be to add stsructure/properties to the horizontal morphisms and squares.
 The corresponding construction on 2-sided displayed categories is described in the file
 `DispCatOnTwoSidedDispCat.v` and it is used to construct several 2-sided displayed categories
 (such as spans and bimodules). However, in order to guarantee that the resulting 2-sided
 displayed category indeed is a double category, several requirements would need to be added to
 guarantee that the resulting 2-sided displayed category has horizontal identities, composition,
 and so on.

 From the description in the previous paragraph, we can deduce what a displayed double
 category would look like: it should consist of two displayed categories (one over the
 vertical category and one over the total category). This notion seems to be quite similar
 to that of a 'double fibration' as in Definition 2.10 in "Double fibrations" by Cruttwell,
 Lambert, Pronk, and Szyld.

 References
 - "Double fibrations" by Cruttwell, Lambert, Pronk, and Szyld

 Contents
 1. The double category
 2. Properties of this double category
 3. Univalence and strictness

 *******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.TwoSidedDispCatOnDispCat.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.
Local Open Scope double_cat.

Section DispCatOnDoubleCat.
  Context (C : double_cat)
          (D : disp_cat C).

  Let E : category := total_category D.

  (** * 1. The double category *)
  Definition double_cat_on_disp_cat_hor_id_data
    : hor_id_data (twosided_disp_cat_on_disp_cat D D (hor_mor C)).
  Proof.
    use make_hor_id_data.
    - exact (λ x, identity_h (pr1 x)).
    - exact (λ x y f, id_h_square _).
  Defined.

  Proposition double_cat_on_disp_cat_hor_id_laws
    : hor_id_laws double_cat_on_disp_cat_hor_id_data.
  Proof.
    split.
    - intro ; cbn.
      apply id_h_square_id.
    - intros ; cbn.
      apply id_h_square_comp.
  Qed.

  Definition double_cat_on_disp_cat_hor_id
    : hor_id (twosided_disp_cat_on_disp_cat D D (hor_mor C)).
  Proof.
    use make_hor_id.
    - exact double_cat_on_disp_cat_hor_id_data.
    - exact double_cat_on_disp_cat_hor_id_laws.
  Defined.

  Definition double_cat_on_disp_cat_hor_comp_data
    : hor_comp_data (twosided_disp_cat_on_disp_cat D D (hor_mor C)).
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f ·h g).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆h s₂).
  Defined.

  Proposition double_cat_on_disp_cat_hor_comp_laws
    : hor_comp_laws double_cat_on_disp_cat_hor_comp_data.
  Proof.
    split.
    - intros ; cbn.
      apply comp_h_square_id.
    - intros ; cbn.
      apply comp_h_square_comp.
  Qed.

  Definition double_cat_on_disp_cat_hor_comp
    : hor_comp (twosided_disp_cat_on_disp_cat D D (hor_mor C)).
  Proof.
    use make_hor_comp.
    - exact double_cat_on_disp_cat_hor_comp_data.
    - exact double_cat_on_disp_cat_hor_comp_laws.
  Defined.

  Definition double_cat_on_disp_cat_lunitor_data
    : double_lunitor_data
        double_cat_on_disp_cat_hor_id
        double_cat_on_disp_cat_hor_comp.
  Proof.
    intros x y f.
    use to_iso_twosided_disp_cat_on_disp_cat.
    exact (lunitor_globular_iso_square f).
  Defined.

  Proposition double_cat_on_disp_cat_lunitor_laws
    : double_lunitor_laws double_cat_on_disp_cat_lunitor_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
    refine (_ @ !(lunitor_square _)).
    use transportb_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition double_cat_on_disp_cat_lunitor
    : double_cat_lunitor
        double_cat_on_disp_cat_hor_id
        double_cat_on_disp_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact double_cat_on_disp_cat_lunitor_data.
    - exact double_cat_on_disp_cat_lunitor_laws.
  Defined.

  Definition double_cat_on_disp_cat_runitor_data
    : double_runitor_data
        double_cat_on_disp_cat_hor_id
        double_cat_on_disp_cat_hor_comp.
  Proof.
    intros x y f.
    use to_iso_twosided_disp_cat_on_disp_cat.
    exact (runitor_globular_iso_square f).
  Defined.

  Proposition double_cat_on_disp_cat_runitor_laws
    : double_runitor_laws double_cat_on_disp_cat_runitor_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
    refine (_ @ !(runitor_square _)).
    use transportb_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition double_cat_on_disp_cat_runitor
    : double_cat_runitor
        double_cat_on_disp_cat_hor_id
        double_cat_on_disp_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact double_cat_on_disp_cat_runitor_data.
    - exact double_cat_on_disp_cat_runitor_laws.
  Defined.

  Definition double_cat_on_disp_cat_associator_data
    : double_associator_data double_cat_on_disp_cat_hor_comp.
  Proof.
    intros w x y z h₁ h₂ h₃.
    use to_iso_twosided_disp_cat_on_disp_cat.
    exact (associator_globular_iso_square h₁ h₂ h₃).
  Defined.

  Proposition double_cat_on_disp_cat_associator_laws
    : double_associator_laws double_cat_on_disp_cat_associator_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
    refine (_ @ !(lassociator_square _ _ _)).
    use transportb_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition double_cat_on_disp_cat_associator
    : double_cat_associator double_cat_on_disp_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact double_cat_on_disp_cat_associator_data.
    - exact double_cat_on_disp_cat_associator_laws.
  Defined.

  Proposition double_cat_on_disp_cat_triangle
    : triangle_law
        double_cat_on_disp_cat_lunitor
        double_cat_on_disp_cat_runitor
        double_cat_on_disp_cat_associator.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
    refine (double_triangle _ _ @ _).
    use transportb_disp_mor2_eq.
    apply idpath.
  Qed.

  Proposition double_cat_on_disp_cat_pentagon
    : pentagon_law double_cat_on_disp_cat_associator.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_twosided_disp_cat_on_disp_cat.
    refine (_ @ double_pentagon _ _ _ _).
    use transportb_disp_mor2_eq.
    apply idpath.
  Qed.

  Definition double_cat_on_disp_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact E.
    - exact (twosided_disp_cat_on_disp_cat D D (hor_mor C)).
    - exact double_cat_on_disp_cat_hor_id.
    - exact double_cat_on_disp_cat_hor_comp.
    - exact double_cat_on_disp_cat_lunitor.
    - exact double_cat_on_disp_cat_runitor.
    - exact double_cat_on_disp_cat_associator.
    - exact double_cat_on_disp_cat_triangle.
    - exact double_cat_on_disp_cat_pentagon.
  Defined.

  (** * 2. Properties of this double category *)
  Definition ver_weq_square_double_cat_on_disp_cat
             (H : ver_weq_square C)
             (HD : locally_propositional D)
    : ver_weq_square double_cat_on_disp_cat.
  Proof.
    intros x y f g.
    cbn in x, y, f, g.
    use weqhomot.
    - refine (make_weq _ (H (pr1 x) (pr1 y) (pr1 f) (pr1 g)) ∘ path_sigma_hprop _ _ _ _)%weq.
      apply HD.
    - intro p.
      induction p ; cbn.
      apply idpath.
  Qed.

  Definition all_companions_double_cat_on_disp_cat
             (H : all_companions_double_cat C)
    : all_companions_double_cat double_cat_on_disp_cat.
  Proof.
    intros x y f.
    pose (c := H (pr1 x) (pr1 y) (pr1 f)).
    simple refine (_ ,, _).
    - exact (pr1 c).
    - use make_double_cat_are_companions.
      + exact (pr12 c).
      + exact (pr122 c).
      + abstract
          (refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           refine (_ @ pr1 (pr222 c)) ;
           use transportf_disp_mor2_eq ;
           apply maponpaths_2 ;
           refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           use transportf_disp_mor2_eq ;
           apply idpath).
      + abstract
          (refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           refine (_ @ pr2 (pr222 c)) ;
           use transportf_disp_mor2_eq ;
           refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           use transportf_disp_mor2_eq ;
           apply idpath).
  Defined.

  Definition all_conjoints_double_cat_on_disp_cat
             (H : all_conjoints_double_cat C)
    : all_conjoints_double_cat double_cat_on_disp_cat.
  Proof.
    intros x y f.
    pose (c := H (pr1 x) (pr1 y) (pr1 f)).
    simple refine (_ ,, _).
    - exact (pr1 c).
    - use make_double_cat_are_conjoints.
      + exact (pr12 c).
      + exact (pr122 c).
      + abstract
          (refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           refine (_ @ pr1 (pr222 c)) ;
           use transportf_disp_mor2_eq ;
           apply maponpaths ;
           refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           use transportf_disp_mor2_eq ;
           apply idpath).
      + abstract
          (refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           refine (_ @ pr2 (pr222 c)) ;
           use transportf_disp_mor2_eq ;
           refine (transportf_disp_mor2_twosided_disp_cat_on_disp_cat _ _ _ _ _ _ @ _) ;
           use transportf_disp_mor2_eq ;
           apply idpath).
  Defined.
End DispCatOnDoubleCat.

(** * 3. Univalence and strictness *)
Definition univalent_double_cat_on_disp_cat
           (C : univalent_double_cat)
           (D : disp_univalent_category C)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (double_cat_on_disp_cat C D).
  - split.
    + use is_univalent_total_category.
      * apply univalent_category_is_univalent.
      * apply disp_univalent_category_is_univalent_disp.
    + use is_univalent_twosided_disp_cat_on_disp_cat.
      apply is_univalent_twosided_disp_cat_hor_mor.
Defined.

Definition pseudo_double_set_cat_on_disp_cat
           (C : pseudo_double_setcat)
           (D : disp_cat C)
           (HD : ∏ (x : C), isaset (D x))
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (double_cat_on_disp_cat C D).
  - split.
    + use isaset_total2.
      * apply (is_setcategory_vertical_cat C).
      * exact HD.
    + apply homset_property.
  - intros x y.
    apply (is_strict_twosided_disp_cat_hor_mor C).
Defined.
