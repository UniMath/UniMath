(************************************************************************************************

 The category of setgroupoids

 In this file, we define the category of setgroupoids, which are groupoids whose type of objects
 is a set. We also characterize the isomorphisms in this category and we prove that this category
 is univalent.

 At first instance, this might seem as the `wrong' thing to do in univalent foundations. After
 all, we have univalent groupoids (aka 1-types), and it is generally better to work with those. The key
 difference between univalent groupoids and setgroupoids is that the former is identified up to
 adjoint equivalence, whereas the latter is identified up to isomorphism of groupoids. This
 difference is quite fundamental, and one consequence is that we have a univalent bicategory of
 univalent groupoids, and a univalent category of setgroupoids.

 This difference also affects how one incarnates the groupoid model of type theory. We have
 at least two ways to define the groupoid model:
 - As a univalent bicategory. Contexts are interpreted as univalent groupoids.
 - As a univalent category. Contexts are interpreted as setgroupoids.
 If we study the groupoid model as a univalent bicategory, then we necessarily get a
 2-dimensional syntax. However, if our goal is to develop a 1-dimensional syntax, then we can
 use setgroupoids instead. For this reason, we define the univalent category of setgroupoids in
 this file.

 Note that one would usually define the category of setgroupoids as a full subcategory of the
 category of setcategories, we take a difference approach here. This is because the definitions
 of full subcategory of some category `C` in UniMath do not have exactly the same morphisms as
 `C`, but instead they also have contain an element of the unit type. Since we want the morphisms
 between setgroupoids to exactly be functors, we define this category by hand. However, we reuse
 the laws of the category of setcategories.

 References
 - 'Bicategorical type theory: semantics and syntax' by Ahrens, North, Van der Weide
 - 'Two-dimensional models of type theory' by Garner
 - 'The groupoid interpretation of type theory' by Hofmann and Streicher

 Content
 1. Groupoids whose objects form a set
 2. The category of setgroupoids
 3. Isomorphisms
 4. The univalent category of setgroupoids

 ************************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.

Local Open Scope cat.

(** * 1. Groupoids whose objects form a set *)
Definition setgroupoid
  : UU
  := ∑ (C : setcategory), is_pregroupoid C.

Definition make_setgroupoid
           (C : setcategory)
           (HC : is_pregroupoid C)
  : setgroupoid
  := C ,, HC.

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

(** * 2. The category of setgroupoids *)
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

(** * 3. Isomorphisms *)
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

(** * 4. The univalent category of setgroupoids *)
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
