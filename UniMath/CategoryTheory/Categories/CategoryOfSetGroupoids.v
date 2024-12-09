Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.

Local Open Scope cat.

Definition setgroupoid
  : UU
  := ∑ (C : setcategory), is_pregroupoid C.

Coercion setgroupoid_to_setcategory
         (G : setgroupoid)
  : setcategory
  := pr1 G.

Proposition isgroupoid_setgroupoid
            {G : setgroupoid}
            {x y : G}
            (f : x --> y)
  : is_z_isomorphism f.
Proof.
  exact (pr2 G x y f).
Qed.

Definition precat_ob_mor_of_setgroupoid
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact setgroupoid.
  - exact (λ (G₁ G₂ : setgroupoid), cat_of_setcategory ⟦ pr1 G₁ , pr1 G₂ ⟧).
Defined.

Definition precat_data_of_setgroupoid
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact precat_ob_mor_of_setgroupoid.
  - exact (λ (G : setgroupoid), functor_identity G).
  - exact (λ _ _ _ (F₁ : _ ⟶ _) (F₂ : _ ⟶ _), F₁ ∙ F₂).
Defined.

Proposition is_precategory_cat_of_setgroupoid
  : is_precategory precat_data_of_setgroupoid.
Proof.
  use make_is_precategory_one_assoc.
  - intros G₁ G₂ F.
    apply (id_left (C := cat_of_setcategory)).
  - intros G₁ G₂ F.
    apply (id_right (C := cat_of_setcategory)).
  - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃.
    apply (assoc (C := cat_of_setcategory)).
Qed.

Definition precat_of_setgroupoid
  : precategory.
Proof.
  use make_precategory.
  - exact precat_data_of_setgroupoid.
  - exact is_precategory_cat_of_setgroupoid.
Defined.

Proposition has_homsets_setgroupoid
  : has_homsets precat_ob_mor_of_setgroupoid.
Proof.
  intros G₁ G₂.
  apply (homset_property cat_of_setcategory).
Qed.

Definition cat_of_setgroupoid
  : category.
Proof.
  use make_category.
  - exact precat_of_setgroupoid.
  - exact has_homsets_setgroupoid.
Defined.


Section Isomorphism.
  Context {G₁ G₂ : cat_of_setgroupoid}
          (F : G₁ --> G₂).

  Proposition to_iso_of_set_groupoid
              (HF : is_z_isomorphism (C := cat_of_setcategory) F)
    : is_z_isomorphism F.
  Proof.
    pose (Fi := (F ,, HF) : z_iso _ _).
    use make_is_z_isomorphism.
    - exact (inv_from_z_iso Fi).
    - abstract
        (split ;
         [ apply (z_iso_inv_after_z_iso Fi) | apply (z_iso_after_z_iso_inv Fi)]).
  Defined.

  Proposition from_iso_of_set_groupoid
              (HF : is_z_isomorphism F)
    :is_z_isomorphism (C := cat_of_setcategory) F.
  Proof.
    pose (Fi := (F ,, HF) : z_iso _ _).
    use make_is_z_isomorphism.
    - exact (inv_from_z_iso Fi).
    - abstract
        (split ;
         [ apply (z_iso_inv_after_z_iso Fi) | apply (z_iso_after_z_iso_inv Fi)]).
  Defined.
End Isomorphism.

Proposition is_univalent_cat_of_setgroupoid
  : is_univalent cat_of_setgroupoid.
Proof.
  intros G₁ G₂.
  use weqhomot.
  - refine (_
            ∘ make_weq _ (is_univalent_cat_of_setcategory (pr1 G₁) (pr1 G₂))
            ∘ path_sigma_hprop _ _ _ _)%weq.
    + apply isaprop_is_pregroupoid.
    + use weqfibtototal.
      intro F.
      use weqimplimpl.
      * apply to_iso_of_set_groupoid.
      * apply from_iso_of_set_groupoid.
      * apply isaprop_is_z_isomorphism.
      * apply isaprop_is_z_isomorphism.
  - intro p.
    induction p.
    use z_iso_eq.
    cbn.
    apply idpath.
Qed.

Definition univalent_cat_of_setgroupoid
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact cat_of_setgroupoid.
  - exact is_univalent_cat_of_setgroupoid.
Defined.
