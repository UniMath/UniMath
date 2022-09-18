(*******************************************************************************

 The Grothendieck construction

 Suppose we have a strict functor `F : C ⟶ StrictCat` where `C` is a strict
 category. Then we can define a strict category `∫ F`, called the Grothendieck
 construction. In this file, we construct this category

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.

Local Open Scope cat.

Definition total_precategory_ob_mor_of_set_functor
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : precategory_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (∑ (x : ob C), ob (pr1 (F x))).
  - exact (λ x y, ∑ (f : pr1 x --> pr1 y), pr1 (#F f) (pr2 x) --> pr2 y).
Defined.

Definition eq_in_set_fiber
           {C : setcategory}
           {F : C ⟶ cat_of_setcategory}
           {x₁ x₂ : C}
           {f g : F x₁ --> F x₂}
           (p : f = g)
           (y : pr1 (F x₁))
  : pr11 f y = pr11 g y.
Proof.
  exact (eqtohomot (maponpaths (λ z, pr11 z) p) y).
Qed.

Definition total_precategory_data_of_set_functor
           {C : setcategory}
           (F : C ⟶ cat_of_setcategory)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (total_precategory_ob_mor_of_set_functor F).
  - refine (λ x, identity _ ,, _).
    apply idtoiso.
    exact (eq_in_set_fiber (functor_id F (pr1 x)) (pr2 x)).
  - refine (λ x y z f g, pr1 f · pr1 g ,, _ · # (pr1 (# F (pr1 g))) (pr2 f) · pr2 g).
    apply idtoiso.
    exact (eq_in_set_fiber (functor_comp F (pr1 f) (pr1 g)) (pr2 x)).
Defined.

Definition eq_mor_category_of_set_functor
           {C : setcategory}
           {F : C ⟶ cat_of_setcategory}
           {x y : total_precategory_data_of_set_functor F}
           {f g : x --> y}
           (p : pr1 f = pr1 g)
           (q : pr2 f = idtoiso (maponpaths (λ z, pr1 (#F z) (pr2 x)) p) · pr2 g)
  : f = g.
Proof.
  induction f as [ f₁ f₂ ].
  induction g as [ g₁ g₂ ].
  cbn in p, q.
  induction p.
  apply maponpaths.
  cbn in q.
  rewrite id_left in q.
  exact q.
Qed.

Definition eq_mor_category_of_set_functor_pr1
          {C : setcategory}
          {F : C ⟶ cat_of_setcategory}
          {x y : total_precategory_data_of_set_functor F}
          {f g : x --> y}
          (p : f = g)
  : pr1 f = pr1 g.
Proof.
  exact (base_paths _ _ p).
Defined.

Definition eq_mor_category_of_set_functor_pr2
          {C : setcategory}
          {F : C ⟶ cat_of_setcategory}
          {x y : total_precategory_data_of_set_functor F}
          {f g : x --> y}
          (p : f = g)
  : pr2 f
    =
    idtoiso
      (maponpaths
         (λ z, pr1 (#F z) (pr2 x))
         (eq_mor_category_of_set_functor_pr1 p))
    · pr2 g.
Proof.
  induction p.
  cbn.
  exact (!(id_left _)).
Qed.


Definition is_precategory_total_of_set_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_precategory (total_precategory_data_of_set_functor F).
Proof.
  use make_is_precategory_one_assoc.
  - intros x y f ; cbn.
    use eq_mor_category_of_set_functor ; cbn.
    + apply id_left.
    + apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (pr1_maponpaths_idtoiso
                 (# F (pr1 f))
                 (eq_in_set_fiber (functor_id F (pr1 x)) (pr2 x))).
      }
      etrans.
      {
        refine (!_).
        exact (pr1_idtoiso_concat
                 (eq_in_set_fiber (functor_comp F _ (pr1 f)) (pr2 x))
                 _).
      }
      apply setcategory_eq_idtoiso.
  - intros x y f ; cbn.
    use eq_mor_category_of_set_functor ; cbn.
    + apply id_right.
    + etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (from_eq_cat_of_setcategory (functor_id F (pr1 y)) (pr2 f)).
      }
      cbn.
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        exact (!(pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp F (pr1 f) _) (pr2 x))
                   _)).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            exact (!(pr1_idtoiso_concat
                       _
                       (eq_in_set_fiber (functor_id F (pr1 y)) (pr2 y)))).
          }
          apply setcategory_refl_idtoiso.
        }
        apply id_right.
      }
      apply maponpaths_2.
      apply setcategory_eq_idtoiso.
  - intros w x y z f g h ; cbn.
    use eq_mor_category_of_set_functor ; cbn.
    + apply assoc.
    + refine (assoc _ _ _ @ _ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply functor_comp.
      }
      do 2 refine (assoc _ _ _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (from_eq_cat_of_setcategory (functor_comp F (pr1 g) (pr1 h)) (pr2 f)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        exact (!(pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp F (pr1 g) (pr1 h)) (pr2 x)))).
      }
      do 2 refine (assoc _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (!(pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp F (pr1 f) (pr1 g · pr1 h)) (pr2 w))
                   _)).
      }
      refine (!_).
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp F (pr1 f · pr1 g) (pr1 h)) (pr2 w)))).
      }
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply setcategory_refl_idtoiso.
        }
        apply id_right.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply functor_comp.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (!(pr1_maponpaths_idtoiso
                   (# F (pr1 h))
                   (eq_in_set_fiber (functor_comp F (pr1 f) (pr1 g)) (pr2 w)))).
      }
      etrans.
      {
        refine (!_).
        exact (pr1_idtoiso_concat
                 (maponpaths
                    (λ q,
                      pr1 (# F q) (pr2 w)) (assoc (pr1 f) (pr1 g) (pr1 h))
                      @ eq_in_set_fiber (functor_comp F (pr1 f · pr1 g) (pr1 h)) (pr2 w))
                 _).
      }
      apply setcategory_eq_idtoiso.
Qed.

Definition total_precategory_of_set_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : precategory.
Proof.
  use make_precategory.
  - exact (total_precategory_data_of_set_functor F).
  - exact (is_precategory_total_of_set_functor F).
Defined.

Definition is_setcategory_total_of_set_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_setcategory (total_precategory_of_set_functor F).
Proof.
  split.
  - apply isaset_total2.
    + apply C.
    + intro.
      apply (F x).
  - intros x y.
    apply isaset_total2.
    + apply homset_property.
    + intro.
      apply homset_property.
Defined.

Definition total_setcategory_of_set_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : setcategory.
Proof.
  simple refine (_ ,, _).
  - exact (total_precategory_of_set_functor F).
  - exact (is_setcategory_total_of_set_functor F).
Defined.
