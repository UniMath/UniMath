(**********************************************************************************

 The double category of structured cospans

 In this file, we define the double category of structured cospans. Suppose that
 we have categories `A` and `X` such that `X` has pushouts and suppose that we also
 have a functor `L : A ⟶ X`. The double category of structured cospans is defined
 as follows:
 - Objects: objects of `A`
 - Vertical morphisms: morphisms in `A`
 - Horizontal morphisms from `a` to `b`: structured cospans. Concretely, an object
   `x`  together with morphisms `L a --> x <-- L b`.
 - The squares from `L a₁ <-- x₁ --> L b₁` to `L a₂ <-- x₂ --> L b₂` whose vertical
   sides are `f : a₁ --> a₂` and `g : b₁ --> b₂` are morphisms `φ : x₁ --> x₂` such
   that the following squares commute

         L a₁ <-- x₁ --> L b₂
          |       |       |
          V       V       V
         L a₂ <-- x₂ --> L b₂

 Identities and composition of vertical morphisms is inherited from `A`. The
 identity structured cospans is `L a <-- L a --> L a`, and the composition of
 structured cospans is given by taking a pushout.

 A reference for this construction is Theorem 3.1 in "Structured Versus Decorated
 Cospans" by Baez, Courser, and Vasilakopoulou.
    https://compositionality-journal.org/papers/compositionality-4-3/pdf
 Note: we do not show that this double category is monoidal.

 Contents
 1. Horizontal identities
 2. Horizontal composition
 3. The unitors and associators
 4. The triangle and pentagon equations
 5. The double category of structured cospans

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.StructuredCospans.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
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

Section StructuredCospansDoubleCat.
  Context {A X : category}
          (PX : Pushouts X)
          (L : A ⟶ X).

  (** * 1. Horizontal identities *)
  Definition structured_cospans_double_cat_hor_id_data
    : hor_id_data (twosided_disp_cat_of_struct_cospans L).
  Proof.
    use make_hor_id_data.
    - exact (id_struct_cospan L).
    - exact (λ x y f, id_struct_cospan_mor L f).
  Defined.

  Proposition structured_cospans_double_cat_hor_id_laws
    : hor_id_laws structured_cospans_double_cat_hor_id_data.
  Proof.
    split.
    - intros a.
      use struct_cospan_sqr_eq ; cbn.
      apply functor_id.
    - intros a₁ a₂ a₃ f g.
      use struct_cospan_sqr_eq ; cbn.
      apply functor_comp.
  Qed.

  Definition structured_cospans_double_cat_hor_id
    : hor_id (twosided_disp_cat_of_struct_cospans L).
  Proof.
    use make_hor_id.
    - exact structured_cospans_double_cat_hor_id_data.
    - exact structured_cospans_double_cat_hor_id_laws.
  Defined.

  (** * 2. Horizontal composition *)
  Definition structured_cospans_double_cat_hor_comp_data
    : hor_comp_data (twosided_disp_cat_of_struct_cospans L).
  Proof.
    use make_hor_comp_data.
    - exact (λ a₁ a₂ a₃ s t, comp_struct_cospan L PX s t).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, comp_struct_cospan_mor L PX s₁ s₂).
  Defined.

  Proposition structured_cospans_double_cat_hor_comp_laws
    : hor_comp_laws structured_cospans_double_cat_hor_comp_data.
  Proof.
    split.
    - intros a₁ a₂ a₃ h₁ h₂.
      use struct_cospan_sqr_eq.
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
      + unfold mor_of_comp_struct_cospan_mor.
        rewrite PushoutArrow_PushoutIn1 ; cbn.
        rewrite id_left, id_right.
        apply idpath.
      + unfold mor_of_comp_struct_cospan_mor.
        rewrite PushoutArrow_PushoutIn2 ; cbn.
        rewrite id_left, id_right.
        apply idpath.
    - intros.
      use struct_cospan_sqr_eq.
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
      + rewrite !assoc.
        unfold mor_of_comp_struct_cospan_mor.
        rewrite !PushoutArrow_PushoutIn1 ; cbn.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn1.
        rewrite !assoc.
        apply idpath.
      + rewrite !assoc.
        unfold mor_of_comp_struct_cospan_mor.
        rewrite !PushoutArrow_PushoutIn2 ; cbn.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn2.
        rewrite !assoc.
        apply idpath.
  Qed.

  Definition structured_cospans_double_cat_hor_comp
    : hor_comp (twosided_disp_cat_of_struct_cospans L).
  Proof.
    use make_hor_comp.
    - exact structured_cospans_double_cat_hor_comp_data.
    - exact structured_cospans_double_cat_hor_comp_laws.
  Defined.

  (** * 3. The unitors and associators *)
  Definition structured_cospans_double_cat_lunitor_data
    : double_lunitor_data
        structured_cospans_double_cat_hor_id
        structured_cospans_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (struct_cospan_lunitor L PX h).
    - use is_iso_twosided_disp_struct_cospan_sqr ; cbn.
      apply is_z_iso_struct_cospan_lunitor_mor.
  Defined.

  Proposition structured_cospans_double_cat_lunitor_laws
    : double_lunitor_laws structured_cospans_double_cat_lunitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ sq.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
    - rewrite !assoc.
      unfold struct_cospan_lunitor_mor, mor_of_comp_struct_cospan_mor.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn1.
      exact (struct_cospan_sqr_mor_left _ sq).
    - rewrite !assoc.
      unfold struct_cospan_lunitor_mor, mor_of_comp_struct_cospan_mor.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn2.
      rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition structured_cospans_double_cat_lunitor
    : double_cat_lunitor
        structured_cospans_double_cat_hor_id
        structured_cospans_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact structured_cospans_double_cat_lunitor_data.
    - exact structured_cospans_double_cat_lunitor_laws.
  Defined.

  Definition structured_cospans_double_cat_runitor_data
    : double_runitor_data
        structured_cospans_double_cat_hor_id
        structured_cospans_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (struct_cospan_runitor L PX h).
    - use is_iso_twosided_disp_struct_cospan_sqr ; cbn.
      apply is_z_iso_struct_cospan_runitor_mor.
  Defined.

  Proposition structured_cospans_double_cat_runitor_laws
    : double_runitor_laws structured_cospans_double_cat_runitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ sq.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
    - rewrite !assoc.
      unfold struct_cospan_runitor_mor, mor_of_comp_struct_cospan_mor.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn1.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc.
      unfold struct_cospan_runitor_mor, mor_of_comp_struct_cospan_mor.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn2.
      exact (struct_cospan_sqr_mor_right _ sq).
  Qed.

  Definition structured_cospans_double_cat_runitor
    : double_cat_runitor
        structured_cospans_double_cat_hor_id
        structured_cospans_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact structured_cospans_double_cat_runitor_data.
    - exact structured_cospans_double_cat_runitor_laws.
  Defined.

  Definition structured_cospans_double_cat_associator_data
    : double_associator_data structured_cospans_double_cat_hor_comp.
  Proof.
    intros w x y z h₁ h₂ h₃.
    simple refine (_ ,, _).
    - exact (struct_cospan_associator L PX h₁ h₂ h₃).
    - use is_iso_twosided_disp_struct_cospan_sqr ; cbn.
      apply is_z_iso_struct_cospan_associator_mor.
  Defined.

  Proposition structured_cospans_double_cat_associator_laws
    : double_associator_laws structured_cospans_double_cat_associator_data.
  Proof.
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ j₁ j₂ k₁ k₂ vw vx vy vz sq₁ sq₂ sq₃.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
    - rewrite !assoc.
      unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor ; cbn.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn1.
      unfold mor_of_comp_struct_cospan_mor.
      rewrite !assoc.
      rewrite PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn1.
      apply idpath.
    - rewrite !assoc.
      unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor.
      rewrite !PushoutArrow_PushoutIn2.
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
      + rewrite !assoc.
        rewrite PushoutArrow_PushoutIn1.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn1.
        unfold mor_of_comp_struct_cospan_mor.
        rewrite !assoc.
        rewrite PushoutArrow_PushoutIn1.
        rewrite PushoutArrow_PushoutIn2.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn2.
        rewrite PushoutArrow_PushoutIn1.
        apply idpath.
      + rewrite !assoc.
        unfold mor_of_comp_struct_cospan_mor.
        rewrite !PushoutArrow_PushoutIn2.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn2.
        apply idpath.
  Qed.

  Definition structured_cospans_double_cat_associator
    : double_cat_associator structured_cospans_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact structured_cospans_double_cat_associator_data.
    - exact structured_cospans_double_cat_associator_laws.
  Defined.

  (** * 4. The triangle and pentagon equations *)
  Proposition structured_cospans_double_cat_triangle
    : triangle_law
        structured_cospans_double_cat_lunitor
        structured_cospans_double_cat_runitor
        structured_cospans_double_cat_associator.
  Proof.
    intro ; intros.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
    - unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor ; cbn.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite PushoutArrow_PushoutIn1.
      rewrite id_left.
      unfold struct_cospan_runitor_mor.
      rewrite !assoc.
      rewrite PushoutArrow_PushoutIn1.
      apply id_left.
    - unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor ; cbn.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn2.
      unfold struct_cospan_lunitor_mor, struct_cospan_runitor_mor.
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
      + rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn1.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn1.
        rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn2.
        rewrite PushoutSqrCommutes.
        apply idpath.
      + rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn2.
        rewrite !id_left.
        apply idpath.
  Qed.

  Proposition structured_cospans_double_cat_pentagon
    : pentagon_law structured_cospans_double_cat_associator.
  Proof.
    intro ; intros.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
    - unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor ; cbn.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite id_left.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite !PushoutArrow_PushoutIn1.
      unfold struct_cospan_associator_mor.
      rewrite !assoc.
      rewrite PushoutArrow_PushoutIn1.
      apply idpath.
    - unfold struct_cospan_associator_mor, mor_of_comp_struct_cospan_mor ; cbn.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn2.
      unfold struct_cospan_associator_mor.
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
      + rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn1.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn1.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn2.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn1.
          refine (assoc' _ _ _ @ _).
          rewrite !PushoutArrow_PushoutIn1.
          refine (assoc _ _ _ @ _).
          rewrite !PushoutArrow_PushoutIn2.
          apply idpath.
        }
        rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn1.
        apply idpath.
      + rewrite !assoc.
        rewrite !PushoutArrow_PushoutIn2.
        use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
        * rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn1.
          refine (!_).
          rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !assoc.
            rewrite !PushoutArrow_PushoutIn2.
            apply idpath.
          }
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite !PushoutArrow_PushoutIn1.
            refine (assoc' _ _ _ @ _).
            rewrite !PushoutArrow_PushoutIn1.
            refine (assoc _ _ _ @ _).
            rewrite !PushoutArrow_PushoutIn2.
            apply idpath.
          }
          rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn2.
          apply idpath.
        * rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn2.
          refine (!_).
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite !PushoutArrow_PushoutIn2.
            apply idpath.
          }
          rewrite !assoc.
          rewrite !PushoutArrow_PushoutIn2.
          rewrite id_left.
          apply idpath.
  Qed.

  (** * 5. The double category of structured cospans *)
  Definition structured_cospans_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact A.
    - exact (twosided_disp_cat_of_struct_cospans L).
    - exact structured_cospans_double_cat_hor_id.
    - exact structured_cospans_double_cat_hor_comp.
    - exact structured_cospans_double_cat_lunitor.
    - exact structured_cospans_double_cat_runitor.
    - exact structured_cospans_double_cat_associator.
    - exact structured_cospans_double_cat_triangle.
    - exact structured_cospans_double_cat_pentagon.
  Defined.

  Definition structured_cospans_double_cat_ver_weq_square
             (H : fully_faithful L)
    : ver_weq_square structured_cospans_double_cat.
  Proof.
    intros x y f g.
    use isweqimplimpl.
    - cbn.
      intros fg.
      induction fg as [ h [ p q ]].
      rewrite id_left, id_right in p.
      rewrite id_left, id_right in q.
      use (invmaponpathsweq (make_weq _ (H x y))) ; cbn.
      rewrite <- p, q.
      apply idpath.
    - apply homset_property.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      pose (p₁ := pr12 φ₁).
      pose (p₂ := pr12 φ₂).
      cbn in p₁, p₂.
      rewrite id_left, id_right in p₁.
      rewrite id_left, id_right in p₂.
      rewrite p₁.
      rewrite <- p₂.
      apply idpath.
  Qed.

  Definition all_companions_structured_cospans_double_cat
    : all_companions_double_cat structured_cospans_double_cat.
  Proof.
    intros x y f.
    simple refine (_ ,, _).
    - exact (struct_cospan_companion L f).
    - use make_double_cat_are_companions'.
      + exact (struct_cospan_companion_unit L f).
      + exact (struct_cospan_companion_counit L f).
      + abstract
          (use struct_cospan_sqr_eq ;
           refine (transportf_disp_mor2_struct_cospan _ _ _ _ @ _) ;
           cbn ;
           unfold mor_of_comp_struct_cospan_mor, struct_cospan_runitor_mor ;
           cbn ;
           rewrite PushoutArrow_PushoutIn2 ;
           rewrite id_left ;
           rewrite PushoutArrow_PushoutIn2 ;
           apply idpath).
      + abstract
          (use struct_cospan_sqr_eq ;
           refine (transportf_disp_mor2_struct_cospan _ _ _ _ @ _) ;
           cbn ;
           apply id_right).
  Defined.

  Definition all_conjoints_structured_cospans_double_cat
    : all_conjoints_double_cat structured_cospans_double_cat.
  Proof.
    intros x y f.
    simple refine (_ ,, _).
    - exact (struct_cospan_conjoint L f).
    - use make_double_cat_are_conjoints'.
      + exact (struct_cospan_conjoint_unit L f).
      + exact (struct_cospan_conjoint_counit L f).
      + abstract
          (use struct_cospan_sqr_eq ;
           refine (transportf_disp_mor2_struct_cospan _ _ _ _ @ _) ;
           cbn ;
           unfold mor_of_comp_struct_cospan_mor, struct_cospan_lunitor_mor ;
           cbn ;
           rewrite !assoc ;
           rewrite PushoutArrow_PushoutIn1 ;
           rewrite id_left ;
           rewrite PushoutArrow_PushoutIn1 ;
           apply idpath).
      + abstract
          (use struct_cospan_sqr_eq ;
           refine (transportf_disp_mor2_struct_cospan _ _ _ _ @ _) ;
           cbn ;
           apply id_right).
  Defined.
End StructuredCospansDoubleCat.

Definition structured_cospans_univalent_double_cat
           {A X : univalent_category}
           (PX : Pushouts X)
           (L : A ⟶ X)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (structured_cospans_double_cat PX L).
  - split.
    + apply univalent_category_is_univalent.
    + use is_univalent_struct_cospans_twosided_disp_cat.
      apply univalent_category_is_univalent.
Defined.

Definition structured_cospans_pseudo_double_setcat
           {A X : setcategory}
           (PX : Pushouts X)
           (L : A ⟶ X)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (structured_cospans_double_cat PX L).
  - apply A.
  - use is_strict_struct_cospans_twosided_disp_cat.
    apply X.
Defined.
