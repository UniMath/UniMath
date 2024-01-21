(*********************************************************************************************

 Every set bicategory gives rise to a pseudo double setcategory

 In this file, we show that every set bicategory gives rise to pseudo double
 setcategory. Recall that a set bicategory is a bicategory such that the objects
 and the 1-cells form a set. Such a bicategory `B` gives rise to the following
 pseudo double setcategory:
 - Objects: objects in `B`
 - Vertical morphisms: identities of objects in `B`
 - Horizontal morphisms: 1-cells in `B`
 - Squares: 2-cells in `B` (with the proper `idtoiso` inserted)
 Note that the vertical morphisms form a set, because we assume that the objects in
 `B` form a set.

 As an intermediate construction, we first show that every bicategory `B` for which
 the objects form a 1-type, gives rise to a double category ([bicat_to_double_bicat])
 without any requirement on univalence or the objects/horizontal morphisms forming
 a set. Afterwards we instantiate this to setbicategories ([setbicat_to_pseudo_double_bicat]).

 Such a construction would have limited usability for univalent bicategories. If the
 objects in a univalent bicategory forms a 1-type, then there can be at most one
 invertible 2-cell between any two adjoint equivalences, which is a rather harsh
 assumptions. For example, this requirement is not satisfied by the bicategory of
 1-types, of univalent groupoids, and the bicategory of (structured) univalent
 categories. In fact, the objects in a univalent double category must form a 1-type,
 so there cannot be a univalent double category whose type of objects is given by
 1-types, univalent groupoids or univalent categories.

 For univalent 2-categories (i.e., univalent categories enriched in the category
 of strict categories), this construction also has limited usability. For such
 2-categories, we would define the corresponding pseudo double category for a
 univalent 2-category `C`:
 - Objects: objects in `C`
 - Vertical morphisms: isomorphisms of objects in `C` (same as identities)
 - Horizontal morphisms: 1-cells in `C`
 - Squares: 2-cells in `C`
 In this case, the category of objects and vertical morphisms is univalent.
 However, the category of horizontal morphisms and squares is not univalent in
 general. If we would add this requirement, then we also need to require that the
 2-category is locally univalent. However, since the 1-cells form a set, we get
 that there is at most one invertible 2-cell between any two morphisms.

 Content
 1. The underlying category
 2. The 2-sided displayed category of 1-cells
 3. Horizontal identities
 4. Horizontal composition
 5. The unitors and associators
 6. The pentagon and triangle equation
 7. The double category corresponding to a bicategory
 8. The pseudo double setcategory corresponding to a bicategory

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.

Local Open Scope cat.

Section BicatToDoubleCat.
  Context (B : bicat)
          (HB : isofhlevel 3 B).

  (** * 1. The underlying category *)
  Definition bicat_to_category
    : category.
  Proof.
    refine (path_groupoid B _).
    exact HB.
  Defined.

  (** * 2. The 2-sided displayed category of 1-cells *)
  Definition bicat_to_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor bicat_to_category bicat_to_category.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x y : B), x --> y).
    - exact (λ x₁ x₂ y₁ y₂ f g p q, f · idtoiso_2_0 _ _ q ==> idtoiso_2_0 _ _ p · g).
  Defined.

  Definition bicat_to_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp bicat_to_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, runitor _ • linvunitor _).
    - refine (λ x₁ x₂ y₁ y₂ z₁ z₂ f g h p₁ p₂ q₁ q₂ s₁ s₂, _).
      induction p₁, p₂, q₁, q₂ ; cbn in *.
      exact (s₁ • lunitor _ • rinvunitor _ • s₂).
  Defined.

  Definition bicat_to_twosided_disp_cat_data
    : twosided_disp_cat_data bicat_to_category bicat_to_category.
  Proof.
    simple refine (_ ,, _).
    - exact bicat_to_twosided_disp_cat_ob_mor.
    - exact bicat_to_twosided_disp_cat_id_comp.
  Defined.

  Proposition bicat_to_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms bicat_to_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ f g p q s.
      induction p, q ; cbn in *.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite vassocl.
        rewrite linvunitor_lunitor.
        apply id2_right.
      }
      apply runitor_rinvunitor.
    - intros x₁ x₂ y₁ y₂ f g p q s.
      induction p, q ; cbn in *.
      refine (_ @ id2_right _).
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite vassocr.
        rewrite rinvunitor_runitor.
        apply id2_left.
      }
      apply lunitor_linvunitor.
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ f₁ f₂ f₃ f₄ p₁ p₂ p₃ q₁ q₂ q₃ s₁ s₂ s₃.
      induction p₁, p₂, p₃, q₁, q₂, q₃ ; cbn in *.
      rewrite !vassocr.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ f g p q.
      apply cellset_property.
  Qed.

  Definition bicat_to_twosided_disp_cat
    : twosided_disp_cat bicat_to_category bicat_to_category.
  Proof.
    simple refine (_ ,, _).
    - exact bicat_to_twosided_disp_cat_data.
    - exact bicat_to_twosided_disp_cat_axioms.
  Defined.

  (** * 3. Horizontal identities *)
  Definition bicat_to_hor_id_data
    : hor_id_data bicat_to_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - exact (λ x, identity _).
    - refine (λ x y p, _).
      induction p ; cbn.
      apply id2.
  Defined.

  Proposition bicat_to_hor_id_laws
    : hor_id_laws bicat_to_hor_id_data.
  Proof.
    split.
    - intro x ; cbn.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_linvunitor.
      apply idpath.
    - intros x y z p q.
      induction p, q ; cbn.
      rewrite !id2_left, id2_right.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      apply idpath.
  Qed.

  Definition bicat_to_hor_id
    : hor_id bicat_to_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact bicat_to_hor_id_data.
    - exact bicat_to_hor_id_laws.
  Defined.

  (** * 4. Horizontal composition *)
  Definition bicat_to_hor_comp_data
    : hor_comp_data bicat_to_twosided_disp_cat.
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f · g).
    - intros x₁ x₂ y₁ y₂ z₁ z₂ p₁ p₂ p₃ f₁ f₂ g₁ g₂ s₁ s₂.
      induction p₁, p₂, p₃ ; cbn in *.
      exact (rassociator _ _ _
             • (_ ◃ s₂)
             • lassociator _ _ _
             • (s₁ ▹ _)
             • rassociator _ _ _).
  Defined.

  Proposition bicat_to_hor_comp_laws
    : hor_comp_laws bicat_to_hor_comp_data.
  Proof.
    split.
    - intros x y z f g ; cbn.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- linvunitor_assoc.
      rewrite !vassocr.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ p₁ p₂ p₃ p₄ p₅ p₆ f₁ f₂ g₁ g₂ h₁ h₂ s₁ s₂ s₃ s₄.
      induction p₁, p₂, p₃, p₄, p₅, p₆ ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- lunitor_triangle.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite <- rinvunitor_triangle.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker.
      rewrite vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      rewrite <- vcomp_lunitor.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      refine (_ @ lassociator_lassociator _ _ _ _).
      rewrite <- lunitor_triangle.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite lwhisker_vcomp.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2.
      rewrite id2_rwhisker.
      apply id2_right.
  Qed.

  Definition bicat_to_hor_comp
    : hor_comp bicat_to_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact bicat_to_hor_comp_data.
    - exact bicat_to_hor_comp_laws.
  Defined.

  (** * 5. The unitors and associators *)
  Definition bicat_to_lunitor_data
    : double_lunitor_data bicat_to_hor_id bicat_to_hor_comp.
  Proof.
    intros x y f.
    use make_iso_twosided_disp.
    - exact (runitor _).
    - simple refine (_ ,, _ ,, _).
      + exact (runitor _ • linvunitor _ • linvunitor _).
      + abstract
          (cbn ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           refine (_ @ id2_left _) ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rinvunitor_runitor ;
           rewrite id2_left ;
           apply lunitor_linvunitor).
      + abstract
          (cbn ;
           rewrite !vassocl ;
           apply maponpaths ;
           refine (_ @ id2_right _) ;
           apply maponpaths ;
           rewrite rinvunitor_runitor ;
           rewrite id2_right ;
           apply linvunitor_lunitor).
  Defined.

  Proposition bicat_to_lunitor_laws
    : double_lunitor_laws bicat_to_lunitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g p q s.
    induction p, q ; cbn.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite (maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
    rewrite lassociator_rassociator.
    rewrite id2_left.
    rewrite vcomp_lunitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite <- lunitor_triangle.
    rewrite !vassocr.
    rewrite rassociator_lassociator.
    rewrite id2_left.
    rewrite <- vcomp_runitor.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    apply id2_right.
  Qed.

  Definition bicat_to_lunitor
    : double_cat_lunitor bicat_to_hor_id bicat_to_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact bicat_to_lunitor_data.
    - exact bicat_to_lunitor_laws.
  Defined.

  Definition bicat_to_runitor_data
    : double_runitor_data bicat_to_hor_id bicat_to_hor_comp.
  Proof.
    intros x y f.
    use make_iso_twosided_disp.
    - exact (runitor _ • runitor _ • linvunitor _).
    - simple refine (_ ,, _ ,, _).
      + exact (linvunitor _).
      + abstract
          (cbn ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           refine (_ @ id2_left _) ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite linvunitor_lunitor ;
           rewrite id2_left ;
           apply runitor_rinvunitor).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           rewrite linvunitor_lunitor ;
           rewrite id2_left ;
           rewrite rinvunitor_runitor ;
           rewrite id2_left ;
           apply idpath).
  Defined.

  Proposition bicat_to_runitor_laws
    : double_runitor_laws bicat_to_runitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g p q s.
    induction p, q ; cbn.
    rewrite !vassocl.
    rewrite lwhisker_id2.
    rewrite id2_left.
    rewrite !vassocr.
    rewrite rassociator_lassociator.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite (maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite runitor_rinvunitor.
    rewrite id2_left.
    rewrite (maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    rewrite rinvunitor_runitor.
    rewrite id2_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      rewrite lunitor_linvunitor.
      apply id2_right.
    }
    rewrite vcomp_runitor.
    apply idpath.
  Qed.

  Definition bicat_to_runitor
    : double_cat_runitor bicat_to_hor_id bicat_to_hor_comp.
  Proof.
    use make_double_runitor.
    - exact bicat_to_runitor_data.
    - exact bicat_to_runitor_laws.
  Defined.

  Definition bicat_to_associator_data
    : double_associator_data bicat_to_hor_comp.
  Proof.
    intros w x y z f g h.
    use make_iso_twosided_disp.
    - exact (runitor _ • lassociator _ _ _ • linvunitor _).
    - simple refine (_ ,, _ ,, _).
      + exact (runitor _ • rassociator _ _ _ • linvunitor _).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           refine (_ @ id2_right _) ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite linvunitor_lunitor ;
           rewrite id2_left ;
           rewrite rinvunitor_runitor ;
           rewrite id2_left ;
           apply lassociator_rassociator).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           refine (_ @ id2_right _) ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite linvunitor_lunitor ;
           rewrite id2_left ;
           rewrite rinvunitor_runitor ;
           rewrite id2_left ;
           apply rassociator_lassociator).
  Defined.

  Proposition bicat_to_associator_laws
    : double_associator_laws bicat_to_associator_data.
  Proof.
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ f₁ f₂ g₁ g₂ h₁ h₂ p₁ p₂ p₃ p₄ s₁ s₂ s₃.
    induction p₁, p₂, p₃, p₄ ; cbn.
    rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 10 apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      do 10 apply maponpaths_2.
      rewrite lwhisker_hcomp.
      rewrite <- inverse_pentagon_3.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      do 9 apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      apply idpath.
    }
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      do 8 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      rewrite !vassocr.
      rewrite <- vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2.
      apply id2_right.
    }
    rewrite !vassocl.
    do 3 apply maponpaths.
    rewrite !vassocr.
    rewrite inverse_pentagon_7.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    rewrite <- rwhisker_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite pentagon_6.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      rewrite lunitor_linvunitor.
      apply id2_right.
    }
    rewrite !vassocr.
    rewrite inverse_pentagon_7.
    rewrite !vassocl.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition bicat_to_associator
    : double_cat_associator bicat_to_hor_comp.
  Proof.
    use make_double_associator.
    - exact bicat_to_associator_data.
    - exact bicat_to_associator_laws.
  Defined.

  (** * 6. The pentagon and triangle equation *)
  Proposition bicat_to_triangle_law
    : triangle_law bicat_to_lunitor bicat_to_runitor bicat_to_associator.
  Proof.
    intros x y z f g ; cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    do 3 apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite runitor_rwhisker.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor.
    rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite runitor_triangle.
    apply idpath.
  Qed.

  Proposition bicat_to_pentagon_law
    : pentagon_law bicat_to_associator.
  Proof.
    intros v w x y z f g h k ; cbn.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 6 apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- linvunitor_assoc.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- lassociator_lassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite runitor_rwhisker.
    rewrite lwhisker_vcomp.
    rewrite !vassocl.
    rewrite linvunitor_lunitor.
    rewrite id2_right.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    rewrite runitor_triangle.
    rewrite !vassocl.
    do 2 apply maponpaths.
    etrans.
    {
      do 6 apply maponpaths.
      rewrite runitor_triangle.
      apply rinvunitor_runitor.
    }
    rewrite id2_right.
    rewrite !vassocr.
    refine (_ @ id2_left _).
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- lunitor_triangle.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    }
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite linvunitor_lunitor.
    rewrite id2_right.
    rewrite runitor_rwhisker.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply lwhisker_id2.
  Qed.

  (** * 7. The double category corresponding to a bicategory *)
  Definition bicat_to_double_bicat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact bicat_to_category.
    - exact bicat_to_twosided_disp_cat.
    - exact bicat_to_hor_id.
    - exact bicat_to_hor_comp.
    - exact bicat_to_lunitor.
    - exact bicat_to_runitor.
    - exact bicat_to_associator.
    - exact bicat_to_triangle_law.
    - exact bicat_to_pentagon_law.
  Defined.
End BicatToDoubleCat.

(** * 8. The pseudo double setcategory corresponding to a bicategory *)
Definition bisetcat_to_pseudo_double_bicat
           (B : bisetcat)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - refine (bicat_to_double_bicat B _).
    use hlevelntosn.
    exact (globally_strict_bisetcat B).
  - split.
    + intros x y.
      apply globally_strict_bisetcat.
    + intros x y.
      apply isasetaprop.
      apply globally_strict_bisetcat.
  - intros x y.
    apply locally_strict_bisetcat.
Defined.
