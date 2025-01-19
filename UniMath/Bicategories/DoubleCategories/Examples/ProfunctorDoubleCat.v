(*****************************************************************************************

 The double category of profunctors

 In this file, we define the pseudo double category of strict categories, functors, and
 profunctors. Note that we need to use strict categories here. This is because for a
 pseudo double category, we need to have a category of objects and a set of vertical
 morphisms. Since the type of functors between two univalent categories is not necessarily
 a set, univalent categories with functors and profunctors cannot form a pseudo double
 category. Instead they form a Verity double bicategory.

 It is worth noticing that the pseudo double category of strict categories and profunctors
 is univalent. This is because the category of strict categories is univalent and because
 the category of sets is univalent. In addition, most of the ingredients to define this
 double category are already defined in other files, so this file is mainly a recollection
 of facts.

 Contents.
 1. Horizontal identity
 2. Horizontal composition
 3. Unitors and associators
 4. Triangle and pentagon
 5. The univalent pseudo double category of profunctors
 6. Companions and conjoints

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.HSET.SetCoends.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Squares.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ProfunctorTwosidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.

(** * 1. Horizontal identity *)
Definition profunctor_hor_id_data
  : hor_id_data twosided_disp_cat_of_profunctors.
Proof.
  use make_hor_id_data.
  - exact (λ (C : setcategory), id_profunctor C).
  - exact (λ (C₁ C₂ : setcategory) (F : C₁ ⟶ C₂), id_v_profunctor_square F).
Defined.

Proposition profunctor_hor_id_laws
  : hor_id_laws profunctor_hor_id_data.
Proof.
  split.
  - intros C.
    use eq_profunctor_square ; cbn.
    intros.
    apply idpath.
  - intros C₁ C₂ C₃ F G.
    use eq_profunctor_square ; cbn.
    intros.
    apply idpath.
Qed.

Definition profunctor_hor_id
  : hor_id twosided_disp_cat_of_profunctors.
Proof.
  use make_hor_id.
  - exact profunctor_hor_id_data.
  - exact profunctor_hor_id_laws.
Defined.

(** * 2. Horizontal composition *)
Definition profunctor_hor_comp_data
  : hor_comp_data twosided_disp_cat_of_profunctors.
Proof.
  use make_hor_comp_data.
  - exact (λ (C₁ C₂ C₃ : setcategory) (P : C₁ ↛ C₂) (Q : C₂ ↛ C₃), comp_profunctor P Q).
  - refine (λ _ _ _ _ _ _ _ _ _ _ _ _ _ τ θ, comp_v_profunctor_square τ θ).
Defined.

Proposition profunctor_hor_comp_laws
  : hor_comp_laws profunctor_hor_comp_data.
Proof.
  split.
  - intros C D E P Q.
    use eq_profunctor_square.
    intros z x h ; cbn.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply (comp_v_profunctor_square_mor_comm
               (id_h_profunctor_square P) (id_h_profunctor_square Q)).
    }
    cbn.
    apply idpath.
  - intros.
    use eq_profunctor_square.
    intros z x h.
    use mor_from_comp_profunctor_ob_eq.
    clear h.
    intros y h h' ; cbn.
    etrans.
    {
      apply (comp_v_profunctor_square_mor_comm
               (comp_h_profunctor_square s₁ s₁')
               (comp_h_profunctor_square s₂ s₂')).
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply (comp_v_profunctor_square_mor_comm s₁ s₂).
      }
      apply (comp_v_profunctor_square_mor_comm s₁' s₂').
    }
    cbn.
    apply idpath.
Qed.

Definition profunctor_hor_comp
  : hor_comp twosided_disp_cat_of_profunctors.
Proof.
  use make_hor_comp.
  - exact profunctor_hor_comp_data.
  - exact profunctor_hor_comp_laws.
Defined.

(** * 3. Unitors and associators *)
Definition profunctor_lunitor_data
  : double_lunitor_data profunctor_hor_id profunctor_hor_comp.
Proof.
  intros C₁ C₂ P.
  use make_iso_twosided_disp.
  - exact (lunitor_profunctor_square P).
  - use to_iso_twosided_disp_profunctor.
    exact (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P).
Defined.

Proposition profunctor_lunitor_laws
  : double_lunitor_laws profunctor_lunitor_data.
Proof.
  intros C₁ C₂ D₁ D₂ P Q F₁ F₂ τ.
  use eq_profunctor_square.
  intros y x h.
  etrans.
  {
    apply transportf_disp_mor2_profunctors.
  }
  cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         (id_profunctor _) P
         y x
         (λ h,
          τ y x (lunitor_profunctor_nat_trans_mor P y x h))
         (λ h,
          lunitor_profunctor_nat_trans_mor
            Q
            (F₂ y) (F₁ x)
            (comp_v_profunctor_square_mor (id_v_profunctor_square _) τ y x h))).
  clear h.
  intros z h h' ; cbn.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply (comp_v_profunctor_square_mor_comm (id_v_profunctor_square _) τ).
  }
  rewrite !lunitor_profunctor_nat_trans_mor_comm ; cbn.
  rewrite (profunctor_square_rmap τ).
  apply idpath.
Qed.

Definition profunctor_lunitor
  : double_cat_lunitor profunctor_hor_id profunctor_hor_comp.
Proof.
  use make_double_lunitor.
  - exact profunctor_lunitor_data.
  - exact profunctor_lunitor_laws.
Defined.

Definition profunctor_runitor_data
  : double_runitor_data profunctor_hor_id profunctor_hor_comp.
Proof.
  intros C₁ C₂ P.
  use make_iso_twosided_disp.
  - exact (runitor_profunctor_square P).
  - use to_iso_twosided_disp_profunctor.
    exact (is_profunctor_nat_iso_runitor_profunctor_nat_trans P).
Defined.

Proposition profunctor_runitor_laws
  : double_runitor_laws profunctor_runitor_data.
Proof.
  intros C₁ C₂ D₁ D₂ P Q F₁ F₂ τ.
  use eq_profunctor_square.
  intros y x h.
  etrans.
  {
    apply transportf_disp_mor2_profunctors.
  }
  cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         P (id_profunctor _)
         y x
         (λ h,
          τ y x (runitor_profunctor_nat_trans_mor P y x h))
         (λ h,
          runitor_profunctor_nat_trans_mor
            Q
            (F₂ y) (F₁ x)
            (comp_v_profunctor_square_mor τ (id_v_profunctor_square _) y x h))).
  clear h.
  intros z h h' ; cbn.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply (comp_v_profunctor_square_mor_comm τ (id_v_profunctor_square _)).
  }
  rewrite !runitor_profunctor_nat_trans_mor_comm ; cbn.
  rewrite (profunctor_square_lmap τ).
  apply idpath.
Qed.

Definition profunctor_runitor
  : double_cat_runitor profunctor_hor_id profunctor_hor_comp.
Proof.
  use make_double_runitor.
  - exact profunctor_runitor_data.
  - exact profunctor_runitor_laws.
Defined.

Definition profunctor_associator_data
  : double_associator_data profunctor_hor_comp.
Proof.
  intros C₁ C₂ C₃ C₄ P₁ P₂ P₃.
  use make_iso_twosided_disp.
  - exact (associator_profunctor_square P₁ P₂ P₃).
  - use to_iso_twosided_disp_profunctor.
    exact (is_profunctor_nat_iso_associator_profunctor_nat_trans P₁ P₂ P₃).
Defined.

Proposition profunctor_associator_laws
  : double_associator_laws profunctor_associator_data.
Proof.
  intros C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ P₁ P₂ Q₁ Q₂ R₁ R₂ F₁ F₂ F₃ F₄ τ₁ τ₂ τ₃ ; cbn in *.
  use eq_profunctor_square.
  intros x₁ x₂ h.
  etrans.
  {
    apply transportf_disp_mor2_profunctors.
  }
  use mor_from_comp_profunctor_ob_eq ; clear h.
  intros x₃ h k.
  use (mor_from_comp_profunctor_ob_eq
         Q₁ R₁
         x₁ x₃
         (λ k,
           comp_h_profunctor_square
             (associator_profunctor_square P₁ Q₁ R₁)
             (comp_v_profunctor_square (comp_v_profunctor_square τ₁ τ₂) τ₃)
             x₁ x₂
             (comp_profunctor_ob_in P₁ (comp_profunctor Q₁ R₁) x₃ h k))
         (λ k,
          comp_h_profunctor_square
            (comp_v_profunctor_square τ₁ (comp_v_profunctor_square τ₂ τ₃))
            (associator_profunctor_square P₂ Q₂ R₂)
            x₁ x₂
            (comp_profunctor_ob_in P₁ (comp_profunctor Q₁ R₁) x₃ h k))).
  clear k.
  intros y k l ; cbn.
  rewrite associator_profunctor_nat_trans_mor_comm.
  etrans.
  {
    apply maponpaths.
    apply associator_profunctor_nat_trans_mor_ob_comm.
  }
  etrans.
  {
    apply (comp_v_profunctor_square_mor_comm (comp_v_profunctor_square τ₁ τ₂) τ₃).
  }
  cbn.
  etrans.
  {
    apply maponpaths_2.
    apply (comp_v_profunctor_square_mor_comm τ₁ τ₂).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply (comp_v_profunctor_square_mor_comm τ₁ (comp_v_profunctor_square τ₂ τ₃)).
  }
  rewrite associator_profunctor_nat_trans_mor_comm.
  cbn.
  etrans.
  {
    apply maponpaths.
    apply (comp_v_profunctor_square_mor_comm τ₂ τ₃).
  }
  etrans.
  {
    exact (associator_profunctor_nat_trans_mor_ob_comm
             P₂ Q₂ R₂
             (τ₁ x₃ x₂ h)
             (τ₂ y x₃ k)
             (τ₃ x₁ y l)).
  }
  apply idpath.
Qed.

Definition profunctor_associator
  : double_cat_associator profunctor_hor_comp.
Proof.
  use make_double_associator.
  - exact profunctor_associator_data.
  - exact profunctor_associator_laws.
Defined.

(** * 4. Triangle and pentagon *)
Proposition profunctor_triangle_law
  : triangle_law profunctor_lunitor profunctor_runitor profunctor_associator.
Proof.
  intros C₁ C₂ C₃ P Q.
  use eq_profunctor_square.
  intros z x h.
  refine (!_).
  etrans.
  {
    apply transportf_disp_mor2_profunctors.
  }
  cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         P (comp_profunctor (id_profunctor C₂) Q)
         _ _
         (λ h,
          comp_v_profunctor_square_mor
            (id_h_profunctor_square P)
            (lunitor_profunctor_square Q)
            z x
            h)
         (λ h,
          comp_v_profunctor_square_mor
            (runitor_profunctor_square P)
            (id_h_profunctor_square Q)
            z x
            (associator_profunctor_nat_trans_mor
               P (id_profunctor C₂) Q
               z x h))).
  clear h.
  intros y h kl ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         (id_profunctor C₂) Q
         z y
         (λ kl,
          comp_v_profunctor_square_mor
            (id_h_profunctor_square P) (lunitor_profunctor_square Q)
            z x
            (comp_profunctor_ob_in
               P (comp_profunctor (id_profunctor C₂) Q)
               y h kl))
         (λ kl,
          comp_v_profunctor_square_mor
            (runitor_profunctor_square P) (id_h_profunctor_square Q)
            z x
            (associator_profunctor_nat_trans_mor
               P (id_profunctor C₂) Q
               z x
               (comp_profunctor_ob_in
                  P (comp_profunctor (id_profunctor C₂) Q)
                  y h kl)))).
  clear kl.
  intros y' k l ; cbn.
  etrans.
  {
    apply (comp_v_profunctor_square_mor_comm
             (id_h_profunctor_square P) (lunitor_profunctor_square Q)
             z x).
  }
  cbn.
  rewrite lunitor_profunctor_nat_trans_mor_comm.
  rewrite associator_profunctor_nat_trans_mor_comm.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply associator_profunctor_nat_trans_mor_ob_comm.
  }
  etrans.
  {
    apply (comp_v_profunctor_square_mor_comm
             (runitor_profunctor_square P) (id_h_profunctor_square Q)
             z x).
  }
  cbn.
  rewrite runitor_profunctor_nat_trans_mor_comm.
  rewrite comp_profunctor_ob_in_comm.
  apply idpath.
Qed.

Proposition profunctor_pentagon_law
  : pentagon_law profunctor_associator.
Proof.
  intros C₁ C₂ C₃ C₄ C₅ P₁ P₂ P₃ P₄.
  use eq_profunctor_square.
  intros z v h.
  etrans.
  {
    apply transportf_disp_mor2_profunctors.
  }
  use mor_from_comp_profunctor_ob_eq.
  clear h.
  intros w h₁ h.
  cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         P₂ (comp_profunctor P₃ P₄)
         z w
         (λ h,
           associator_profunctor_nat_trans_mor
             (comp_profunctor P₁ P₂) P₃ P₄ z v
             (associator_profunctor_nat_trans_mor P₁ P₂
                (comp_profunctor P₃ P₄) z v
                (comp_profunctor_ob_in P₁
                   (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                   w h₁ h)))
         (λ h,
          comp_v_profunctor_square_mor
            (associator_profunctor_square P₁ P₂ P₃) (id_h_profunctor_square P₄)
            z v
            (associator_profunctor_nat_trans_mor
               P₁ (comp_profunctor P₂ P₃) P₄ z v
               (comp_v_profunctor_square_mor
                  (id_h_profunctor_square P₁) (associator_profunctor_square P₂ P₃ P₄)
                  z v
                  (comp_profunctor_ob_in
                     P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                     w h₁ h))))).
  clear h.
  intros x h₂ h ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₃ P₄
         z x
         (λ h,
           associator_profunctor_nat_trans_mor
             (comp_profunctor P₁ P₂) P₃ P₄ z v
             (associator_profunctor_nat_trans_mor
                P₁ P₂ (comp_profunctor P₃ P₄) z v
                (comp_profunctor_ob_in
                   P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                   w h₁
                   (comp_profunctor_ob_in
                      P₂ (comp_profunctor P₃ P₄) x h₂ h))))
         (λ h,
          comp_v_profunctor_square_mor
            (associator_profunctor_square P₁ P₂ P₃) (id_h_profunctor_square P₄)
            z v
            (associator_profunctor_nat_trans_mor
               P₁ (comp_profunctor P₂ P₃) P₄ z v
               (comp_v_profunctor_square_mor
                  (id_h_profunctor_square P₁) (associator_profunctor_square P₂ P₃ P₄)
                  z v
                  (comp_profunctor_ob_in
                     P₁ (comp_profunctor P₂ (comp_profunctor P₃ P₄))
                     w h₁
                     (comp_profunctor_ob_in
                        P₂ (comp_profunctor P₃ P₄)
                        x h₂ h)))))).
  clear h.
  intros y h₃ h₄ ; cbn.
  etrans.
  {
    rewrite associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      apply maponpaths.
      apply (associator_profunctor_nat_trans_mor_ob_comm P₁ P₂ (comp_profunctor P₃ P₄)).
    }
    rewrite associator_profunctor_nat_trans_mor_comm.
    exact (associator_profunctor_nat_trans_mor_ob_comm
             (comp_profunctor P₁ P₂) P₃ P₄
             (comp_profunctor_ob_in P₁ P₂ w h₁ h₂)
             h₃
             h₄).
  }
  refine (!_).
  etrans.
  {
    etrans.
    {
      do 2 apply maponpaths.
      apply (comp_v_profunctor_square_mor_comm
               (id_h_profunctor_square P₁)
               (associator_profunctor_square P₂ P₃ P₄)).
    }
    cbn.
    rewrite !associator_profunctor_nat_trans_mor_comm.
    etrans.
    {
      do 2 apply maponpaths.
      apply associator_profunctor_nat_trans_mor_ob_comm.
    }
    etrans.
    {
      apply maponpaths.
      apply associator_profunctor_nat_trans_mor_ob_comm.
    }
    etrans.
    {
      apply (comp_v_profunctor_square_mor_comm
               (associator_profunctor_square P₁ P₂ P₃)
               (id_h_profunctor_square P₄)).
    }
    cbn.
    rewrite associator_profunctor_nat_trans_mor_comm.
    apply maponpaths_2.
    apply associator_profunctor_nat_trans_mor_ob_comm.
  }
  apply idpath.
Qed.

(** * 5. The univalent pseudo double category of profunctors *)
Definition setcat_profunctor_double_cat
  : double_cat.
Proof.
  use make_double_cat.
  - exact cat_of_setcategory.
  - exact twosided_disp_cat_of_profunctors.
  - exact profunctor_hor_id.
  - exact profunctor_hor_comp.
  - exact profunctor_lunitor.
  - exact profunctor_runitor.
  - exact profunctor_associator.
  - exact profunctor_triangle_law.
  - exact profunctor_pentagon_law.
Defined.

Definition setcat_profunctor_univalent_double_cat
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact setcat_profunctor_double_cat.
  - split.
    + exact is_univalent_cat_of_setcategory.
    + exact is_univalent_twosided_disp_cat_of_profunctors.
Defined.

(** * 6. Companions and conjoints *)
Definition all_companions_setcat_profunctor_double_cat
  : all_companions_double_cat setcat_profunctor_double_cat.
Proof.
  intros C₁ C₂ F.
  refine (representable_profunctor_left F ,, _).
  use make_double_cat_are_companions'.
  - exact (representable_profunctor_left_unit F).
  - exact (representable_profunctor_left_counit F).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ;
       refine (transportf_disp_mor2_profunctors _ _ _ _ @ _) ;
       cbn ;
       etrans ;
       [ apply maponpaths ;
         apply (comp_v_profunctor_square_mor_comm
                  (representable_profunctor_left_counit F)
                  (representable_profunctor_left_unit F))
       | ] ;
       rewrite runitor_profunctor_nat_trans_mor_comm ;
       cbn ;
       rewrite !functor_id ;
       rewrite !id_right ;
       apply idpath).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ;
       etrans ; [ apply transportf_disp_mor2_profunctors | ] ;
       cbn ;
       apply idpath).
Defined.

Definition all_conjoints_setcat_profunctor_double_cat
  : all_conjoints_double_cat setcat_profunctor_double_cat.
Proof.
  intros C₁ C₂ F.
  refine (representable_profunctor_right F ,, _).
  use make_double_cat_are_conjoints'.
  - exact (representable_profunctor_right_unit F).
  - exact (representable_profunctor_right_counit F).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ;
       refine (transportf_disp_mor2_profunctors _ _ _ _ @ _) ;
       cbn ;
       etrans ;
       [ apply maponpaths ;
         apply (comp_v_profunctor_square_mor_comm
                  (representable_profunctor_right_counit F)
                  (representable_profunctor_right_unit F))
       | ] ;
       rewrite lunitor_profunctor_nat_trans_mor_comm ;
       cbn ;
       rewrite !functor_id ;
       rewrite !id_left ;
       apply idpath).
  - abstract
      (use eq_profunctor_square ;
       intros y x h ;
       etrans ; [ apply transportf_disp_mor2_profunctors | ] ;
       cbn ;
       apply idpath).
Defined.
