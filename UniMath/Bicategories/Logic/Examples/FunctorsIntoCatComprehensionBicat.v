(*******************************************************************

 The comprehension bicategory of functors into categories

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.Examples.FibrationsInStrictCats.
Require Import UniMath.Bicategories.Core.Examples.StrictCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FunctorsIntoCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FunctorsIntoCatCleaving.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.


Definition pr1_idtoiso_concat
          {C : category}
          {x y z : C}
          (f : x = y) (g : y = z)
  : pr1 (idtoiso (f @ g)) = pr1 (idtoiso f) · pr1 (idtoiso g).
Proof.
  exact (maponpaths pr1 (idtoiso_concat _ _ _ _ f g)).
Qed.

Definition pr1_maponpaths_idtoiso
          {C D : category}
          (F : C ⟶ D)
          {a b : C}
          (e : a = b)
  : pr1 (idtoiso (maponpaths F e)) = #F (pr1 (idtoiso e)).
Proof.
  exact (maponpaths pr1 (maponpaths_idtoiso _ _ F _ _ e)).
Qed.

Definition setcategory_eq_idtoiso
          {C : setcategory}
          {x y : C}
          (p q : x = y)
  : pr1 (idtoiso p) = pr1 (idtoiso q).
Proof.
  do 2 apply maponpaths.
  apply C.
Qed.

Definition setcategory_refl_idtoiso
          {C : setcategory}
          {x : C}
          (p : x = x)
  : pr1 (idtoiso p) = identity _.
Proof.
  apply (setcategory_eq_idtoiso p (idpath x)).
Qed.

Definition setcategory_eq_idtoiso_comp
          {C : setcategory}
          {x x' y y' : C}
          (p p' : x = x')
          (f : x' --> y)
          (q q' : y = y')
  : idtoiso p · f · idtoiso q
    =
    idtoiso p' · f · idtoiso q'.
Proof.
  etrans.
  {
    apply maponpaths.
    exact (setcategory_eq_idtoiso q q').
  }
  do 2 apply maponpaths_2.
  apply setcategory_eq_idtoiso.
Qed.

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

Definition from_eq_cat_of_setcategory
          {C₁ C₂ : cat_of_setcategory}
          {F₁ F₂ : C₁ --> C₂}
          (p : F₁ = F₂)
          {x₁ x₂ : pr1 C₁}
          (f : x₁ --> x₂)
  : # (pr1 F₁) f
    =
    idtoiso (maponpaths (λ z, pr11 z x₁) p)
    · # (pr1 F₂) f
    · idtoiso (maponpaths (λ z, pr11 z x₂) (!p)).
Proof.
  induction p ; cbn.
  rewrite id_left, id_right.
  apply idpath.
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
                 (eq_in_set_fiber (functor_comp F (id₁ (pr1 x)) (pr1 f)) (pr2 x))
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
                   (eq_in_set_fiber (functor_comp F (pr1 f) (id₁ (pr1 y))) (pr2 x))
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

Definition pr1_total_category_of_set_functor_data
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : functor_data
      (total_setcategory_of_set_functor F)
      C.
Proof.
  use make_functor_data.
  - exact (λ x, pr1 x).
  - exact (λ _ _ f, pr1 f).
Defined.

Definition pr1_total_category_of_set_is_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_functor (pr1_total_category_of_set_functor_data F).
Proof.
  split ; intro ; intros ; apply idpath.
Qed.

Definition pr1_total_category_of_set_functor
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : total_setcategory_of_set_functor F ⟶ C.
Proof.
  use make_functor.
  - exact (pr1_total_category_of_set_functor_data F).
  - exact (pr1_total_category_of_set_is_functor F).
Defined.

Section FunctorTotalCategoryFromSetFunctor.
  Context {C₁ C₂ : setcategory}
         (F : C₁ ⟶ C₂)
         {G₁ : C₁ ⟶ cat_of_setcategory}
         {G₂ : C₂ ⟶ cat_of_setcategory}
         (α : G₁ ⟹ F ∙ G₂).

  Definition functor_total_category_of_set_functor_eq
            {x y : total_precategory_of_set_functor G₁}
            (f : x --> y)
    : pr1 (# G₂ (# F (pr1 f))) (pr1 (pr1 α (pr1 x)) (pr2 x))
      =
      pr1 (α (pr1 y)) (pr1 (# G₁ (pr1 f)) (pr2 x)).
  Proof.
    exact (!(eqtohomot (maponpaths (λ z, pr11 z) (nat_trans_ax α _ _ (pr1 f))) (pr2 x))).
  Qed.

  Definition functor_total_category_of_set_functor_data
    : functor_data
        (total_precategory_of_set_functor G₁)
        (total_precategory_of_set_functor G₂).
  Proof.
    use make_functor_data.
    - exact (λ x, F (pr1 x) ,, pr1 (pr1 α (pr1 x)) (pr2 x)).
    - refine (λ x y f, #F (pr1 f) ,, _).
      exact (idtoiso (functor_total_category_of_set_functor_eq f)
             · # (pr1 (α (pr1 y))) (pr2 f)).
  Defined.

  Definition is_functor_functor_total_category_of_set_functor
    : is_functor functor_total_category_of_set_functor_data.
  Proof.
    split.
    - intro x.
      use eq_mor_category_of_set_functor ; cbn.
      + apply functor_id.
      + etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (pr1_maponpaths_idtoiso
                   (α (pr1 x))
                   (eq_in_set_fiber (functor_id G₁ (pr1 x)) (pr2 x))).
        }
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (maponpaths
                      (pr1 (α (pr1 x)))
                      (eq_in_set_fiber (functor_id G₁ (pr1 x)) (pr2 x)))).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber
                      (functor_id G₂ (F (pr1 x))) (pr1 (pr1 α (pr1 x)) (pr2 x)))).
        }
        apply setcategory_eq_idtoiso.
    - intros x y z f g.
      use eq_mor_category_of_set_functor ; cbn.
      + apply functor_comp.
      + cbn.
        refine (!_).
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber
                      (functor_comp G₂ (# F (pr1 f)) (# F (pr1 g)))
                      (pr1 (pr1 α (pr1 x)) (pr2 x)))).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          etrans.
          {
            apply functor_comp.
          }
          apply maponpaths_2.
          refine (!_).
          apply  (pr1_maponpaths_idtoiso
                    (# G₂ (# F (pr1 g)))
                    (functor_total_category_of_set_functor_eq f)).
        }
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          refine (!_).
          exact (pr1_idtoiso_concat
                   (maponpaths
                      (λ q, pr1 (# G₂ q) (pr1 (pr1 α (pr1 x)) (pr2 x)))
                      (functor_comp F (pr1 f) (pr1 g))
                       @ eq_in_set_fiber
                           (functor_comp G₂ (# F (pr1 f)) (# F (pr1 g)))
                           (pr1 (pr1 α (pr1 x)) (pr2 x)))
                   (maponpaths
                      (pr1 (# G₂ (# F (pr1 g))))
                      (functor_total_category_of_set_functor_eq f))).
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply functor_comp.
          }
          apply maponpaths.
          apply functor_comp.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            exact (pr1_maponpaths_idtoiso
                     (α (pr1 z))
                     (eq_in_set_fiber (functor_comp G₁ (pr1 f) (pr1 g)) (pr2 x))).
          }
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (maponpaths
                      (pr1 (α (pr1 z)))
                      (eq_in_set_fiber (functor_comp G₁ (pr1 f) (pr1 g)) (pr2 x)))).
        }
        etrans.
        {
          apply maponpaths.
          exact (from_eq_cat_of_setcategory
                   (nat_trans_ax α _ _ (pr1 g))
                   (pr2 f)).
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        cbn.
        apply setcategory_eq_idtoiso_comp.
  Qed.

  Definition functor_total_category_of_set_functor
    : total_precategory_of_set_functor G₁ ⟶ total_precategory_of_set_functor G₂.
  Proof.
    use make_functor.
    - exact functor_total_category_of_set_functor_data.
    - exact is_functor_functor_total_category_of_set_functor.
  Defined.

  Definition functor_total_category_of_set_functor_comm
    : pr1_total_category_of_set_functor G₁ ∙ F
      ⟹
      functor_total_category_of_set_functor ∙ pr1_total_category_of_set_functor G₂.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ; cbn ;
         exact (id_right _ @ !(id_left _))).
  Defined.

  Definition is_nat_z_iso_functor_total_category_of_set_functor_comm
    : is_nat_z_iso functor_total_category_of_set_functor_comm.
  Proof.
    intro ; cbn.
    apply identity_is_z_iso.
  Defined.
End FunctorTotalCategoryFromSetFunctor.

Section NatTransTotalCategoryFromNatTrans.
  Context {C₁ C₂ : setcategory}
         {F₁ F₂ : C₁ ⟶ C₂}
         (α : F₁ ⟹ F₂)
         {G₁ : C₁ ⟶ cat_of_setcategory}
         {G₂ : C₂ ⟶ cat_of_setcategory}
         (β₁ : G₁ ⟹ F₁ ∙ G₂)
         (β₂ : G₁ ⟹ F₂ ∙ G₂)
         (p : ∏ (x : C₁), pr1 β₁ x ∙ # (pr1 G₂) (pr1 α x) = pr1 β₂ x).

  Definition nat_trans_total_category_of_set_functor_eq
            (x : total_precategory_of_set_functor G₁)
    : pr1 (# G₂ (α (pr1 x))) (pr1 (pr1 β₁ (pr1 x)) (pr2 x))
      =
      pr1 (pr1 β₂ (pr1 x)) (pr2 x).
  Proof.
    exact (eqtohomot (maponpaths (λ z, pr11 z) (p (pr1 x))) (pr2 x)).
  Qed.

  Definition nat_trans_total_category_of_set_functor_data
    : nat_trans_data
        (functor_total_category_of_set_functor F₁ β₁)
        (functor_total_category_of_set_functor F₂ β₂).
  Proof.
    refine (λ x, α (pr1 x) ,, _).
    exact (idtoiso (nat_trans_total_category_of_set_functor_eq x)).
  Defined.

  Definition nat_trans_total_category_of_set_functor_is_nat_trans
    : is_nat_trans
        _ _
        nat_trans_total_category_of_set_functor_data.
  Proof.
    intros x y f.
    use eq_mor_category_of_set_functor.
    - apply nat_trans_ax.
    - cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# G₂ (α (pr1 y)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp G₂ (# F₁ (pr1 f)) (α (pr1 y)))
                    (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            exact (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber
                        (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                        (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
          }
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# G₂ (# F₂ (pr1 f)))).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (_
                    @ eq_in_set_fiber
                        (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                        (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 ((_
                  @ eq_in_set_fiber
                      (functor_comp G₂ (α (pr1 x)) (# F₂ (pr1 f)))
                      (pr1 (pr1 β₁ (pr1 x)) (pr2 x)))
                  @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (from_eq_cat_of_setcategory (p (pr1 y)) (pr2 f)).
      }
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        exact (pr1_idtoiso_concat
                 _
                 (nat_trans_total_category_of_set_functor_eq y)).
      }
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply pr1_idtoiso_concat.
      }
      etrans.
      {
        apply maponpaths.
        apply setcategory_refl_idtoiso.
      }
      etrans.
      {
        apply id_right.
      }
      apply maponpaths_2.
      apply setcategory_eq_idtoiso.
  Qed.

  Definition nat_trans_total_category_of_set_functor
    : functor_total_category_of_set_functor F₁ β₁
        ⟹
        functor_total_category_of_set_functor F₂ β₂.
  Proof.
    use make_nat_trans.
    - exact nat_trans_total_category_of_set_functor_data.
    - exact nat_trans_total_category_of_set_functor_is_nat_trans.
  Defined.
End NatTransTotalCategoryFromNatTrans.

Definition functor_total_category_of_set_functor_on_id_data
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : nat_trans_data
      (functor_identity _)
      (functor_total_category_of_set_functor
         (functor_identity C)
         (nat_trans_id F))
  := λ _, identity _.

Definition functor_total_category_of_set_functor_on_id_is_nat_trans
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_nat_trans
      _ _
      (functor_total_category_of_set_functor_on_id_data F).
Proof.
  intros x y f.
  refine (id_right _ @ _ @ !(id_left _)).
  use eq_mor_category_of_set_functor.
  - apply idpath.
  - cbn.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply setcategory_refl_idtoiso.
    }
    apply id_left.
Qed.

Definition functor_total_category_of_set_functor_on_id
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : functor_identity _
    ⟹
    functor_total_category_of_set_functor
      (functor_identity C)
      (nat_trans_id F).
Proof.
  use make_nat_trans.
  - exact (functor_total_category_of_set_functor_on_id_data F).
  - exact (functor_total_category_of_set_functor_on_id_is_nat_trans F).
Defined.

Definition is_nat_z_iso_functor_total_category_of_set_functor_on_id
          {C : setcategory}
          (F : C ⟶ cat_of_setcategory)
  : is_nat_z_iso (functor_total_category_of_set_functor_on_id_data F).
Proof.
  intro.
  apply identity_is_z_iso.
Defined.

Definition functor_total_category_of_set_functor_on_comp_data
          {C₁ C₂ C₃ : setcategory}
          {F₁ : C₁ ⟶ C₂}
          {F₂ : C₂ ⟶ C₃}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          {G₃ : C₃ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F₁ ∙ G₂)
          (β : G₂ ⟹ F₂ ∙ G₃)
  : nat_trans_data
      (functor_total_category_of_set_functor F₁ α
       ∙ functor_total_category_of_set_functor F₂ β)
      (functor_total_category_of_set_functor
         (F₁ ∙ F₂)
         (nat_trans_comp _ _ _ α (pre_whisker F₁ β)))
  := λ _, identity _.

Definition functor_total_category_of_set_functor_on_comp_is_nat_trans
          {C₁ C₂ C₃ : setcategory}
          {F₁ : C₁ ⟶ C₂}
          {F₂ : C₂ ⟶ C₃}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          {G₃ : C₃ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F₁ ∙ G₂)
          (β : G₂ ⟹ F₂ ∙ G₃)
  : is_nat_trans
      _ _
      (functor_total_category_of_set_functor_on_comp_data α β).
Proof.
  intros x y f.
  refine (id_right _ @ _ @ !(id_left _)).
  use eq_mor_category_of_set_functor ; cbn.
  - apply idpath.
  - cbn.
    refine (_ @ !(id_left _)).
    etrans.
    {
      apply maponpaths.
      apply functor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (pr1_maponpaths_idtoiso (β (F₁ (pr1 y)))).
    }
    etrans.
    {
      refine (!_).
      exact (pr1_idtoiso_concat
               _
               (maponpaths
                  (pr1 (β (F₁ (pr1 y))))
                  (functor_total_category_of_set_functor_eq F₁ α f))).
    }
    apply setcategory_eq_idtoiso.
Qed.

Definition functor_total_category_of_set_functor_on_comp
          {C₁ C₂ C₃ : setcategory}
          {F₁ : C₁ ⟶ C₂}
          {F₂ : C₂ ⟶ C₃}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          {G₃ : C₃ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F₁ ∙ G₂)
          (β : G₂ ⟹ F₂ ∙ G₃)
  : functor_total_category_of_set_functor F₁ α
    ∙ functor_total_category_of_set_functor F₂ β
    ⟹
    functor_total_category_of_set_functor
      (F₁ ∙ F₂)
      (nat_trans_comp _ _ _ α (pre_whisker F₁ β)).
Proof.
  use make_nat_trans.
  - exact (functor_total_category_of_set_functor_on_comp_data α β).
  - exact (functor_total_category_of_set_functor_on_comp_is_nat_trans α β).
Defined.

Definition is_nat_z_iso_functor_total_category_of_set_functor_on_comp
          {C₁ C₂ C₃ : setcategory}
          {F₁ : C₁ ⟶ C₂}
          {F₂ : C₂ ⟶ C₃}
          {G₁ : C₁ ⟶ cat_of_setcategory}
          {G₂ : C₂ ⟶ cat_of_setcategory}
          {G₃ : C₃ ⟶ cat_of_setcategory}
          (α : G₁ ⟹ F₁ ∙ G₂)
          (β : G₂ ⟹ F₂ ∙ G₃)
  : is_nat_z_iso
      (functor_total_category_of_set_functor_on_comp α β).
Proof.
  intro.
  apply identity_is_z_iso.
Defined.


Section IsOpcartesianTotalSetCategory.
  Context {C : setcategory}
         (G : C ⟶ cat_of_setcategory)
         {e₁ e₂ : total_setcategory_of_set_functor G}
         {f : e₁ --> e₂}
         (Hf : is_z_isomorphism (pr2 f)).

  Section Factorization.
    Context {e₃ : total_setcategory_of_set_functor G}
           (g : e₁ --> e₃)
           (h : pr1 e₂ --> pr1 e₃)
           (p : pr1 g = pr1 f · h).

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_unique
      : isaprop
          (∑ φ, # (pr1_total_category_of_set_functor G) φ = h
               ×
               f · φ = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_mor_category_of_set_functor.
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - pose (q := eq_mor_category_of_set_functor_pr2 (pr22 φ₁ @ !(pr22 φ₂))).
        cbn in q.
        use (cancel_z_iso'
               (# (pr1 (# G (pr11 φ₁))) (pr2 f) ,, _)).
        {
          cbn.
          apply functor_on_is_z_isomorphism.
          exact Hf.
        }
        cbn.
        use (cancel_z_iso'
               (idtoiso
                  (eq_in_set_fiber (functor_comp G (pr1 f) (pr11 φ₁)) (pr2 e₁)))).
        rewrite !assoc.
        refine (q @ _) ; clear q.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (from_eq_cat_of_setcategory
                   (maponpaths (λ z, #G z) (pr12 φ₁ @ !(pr12 φ₂)))
                   (pr2 f)).
        }
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          etrans.
          {
            refine (!_).
            apply (pr1_idtoiso_concat
                     (maponpaths
                      (λ z, (pr11 z) (pr2 e₂))
                      (!(maponpaths
                           (λ z, # G z)
                           (pr12 φ₁ @ ! pr12 φ₂))))).
          }
          apply setcategory_refl_idtoiso.
        }
        rewrite id_right.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply pr1_idtoiso_concat.
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          exact (pr1_idtoiso_concat
                   _
                   (eq_in_set_fiber (functor_comp G (pr1 f) (pr11 φ₂)) (pr2 e₁))).
        }
        apply setcategory_eq_idtoiso.
    Qed.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_eq
      : pr1 (# G h) (pr1 (# G (pr1 f)) (pr2 e₁))
        =
        pr1 (# G (pr1 g)) (pr2 e₁).
    Proof.
      refine (!(eq_in_set_fiber (functor_comp G (pr1 f) h) (pr2 e₁)) @ _).
      apply maponpaths_2.
      do 2 apply maponpaths.
      exact (!p).
    Qed.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor
      : e₂ --> e₃.
    Proof.
      refine (h ,, #(pr1 (#G h)) (inv_from_z_iso (_ ,, Hf)) · idtoiso _ · pr2 g).
      apply is_opcartesian_total_setcategory_of_set_functor_factor_eq.
    Defined.

    Definition is_opcartesian_total_setcategory_of_set_functor_factor_comm
      : f · is_opcartesian_total_setcategory_of_set_functor_factor
        =
        g.
    Proof.
      unfold is_opcartesian_total_setcategory_of_set_functor_factor.
      use eq_mor_category_of_set_functor.
      - cbn.
        exact (!p).
      - cbn.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            refine (!_).
            apply functor_comp.
          }
          etrans.
          {
            apply maponpaths.
            exact (z_iso_inv_after_z_iso (pr2 f ,, Hf)).
          }
          apply functor_id.
        }
        rewrite id_left.
        etrans.
        {
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp G _ _) _)).
        }
        apply setcategory_eq_idtoiso.
    Qed.
  End Factorization.

  Definition is_opcartesian_total_setcategory_of_set_functor
    : is_opcartesian_sopfib
        (pr1_total_category_of_set_functor G)
        f.
  Proof.
    intros e₃ g h p.
    use iscontraprop1.
    - exact (is_opcartesian_total_setcategory_of_set_functor_factor_unique g h).
    - simple refine (_ ,, (_ ,, _)).
      + exact (is_opcartesian_total_setcategory_of_set_functor_factor g h p).
      + abstract
          (cbn ;
           apply idpath).
      + exact (is_opcartesian_total_setcategory_of_set_functor_factor_comm g h p).
  Defined.
End IsOpcartesianTotalSetCategory.

Definition street_opfib_pr1_total_setcategory
          {C : setcategory}
          (G : C ⟶ cat_of_setcategory)
  : street_opfib
      (pr1_total_category_of_set_functor G).
Proof.
  intros x y f.
  simple refine (_ ,, (_ ,, _) ,, _ ,, _).
  - exact (y ,, pr1 (#G f) (pr2 x)).
  - exact (f ,, identity _).
  - apply identity_z_iso.
  - exact (!(id_right f)).
  - apply is_opcartesian_total_setcategory_of_set_functor.
    apply is_z_isomorphism_identity.
Defined.






Definition functors_into_cat_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_functors_into_cat
      (cod_disp_bicat bicat_of_strict_cats)
      (id_psfunctor bicat_of_strict_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C F,
           total_setcategory_of_set_functor F
           ,,
           pr1_total_category_of_set_functor F).
  - refine (λ C₁ C₂ F G₁ G₂ α, functor_total_category_of_set_functor F α ,, _).
    use make_invertible_2cell.
    + exact (functor_total_category_of_set_functor_comm F α).
    + apply is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_comm F α).
  - refine (λ C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂ p,
            nat_trans_total_category_of_set_functor α β₁ β₂ p
            ,,
            _).
    abstract
      (use nat_trans_eq ; [ apply C₂ | ] ;
       intro x ;
       cbn ;
       rewrite id_left, id_right ;
       apply idpath).
  - intros C F.
    simple refine (_ ,, _).
    + simple refine (_ ,, _).
      * exact (functor_total_category_of_set_functor_on_id F).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_on_id F).
  - intros C₁ C₂ C₃ F₁ F₂ G₁ G₂ G₃ α β.
    simple refine (_ ,, _).
    + simple refine (_ ,, _).
      * exact (functor_total_category_of_set_functor_on_comp α β).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ;
           cbn ;
           rewrite !id_left ;
           rewrite (functor_id F₂) ;
           rewrite !id_right ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_invertible_2cell_bicat_of_strict_cat.
      exact (is_nat_z_iso_functor_total_category_of_set_functor_on_comp α β).
Time Defined.

Definition is_disp_psfunctor_functors_into_cat_comprehension
  : is_disp_psfunctor
      _ _ _
      functors_into_cat_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + apply idpath.
    + cbn.
      refine (_ @ !(id_left _)).
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + apply idpath.
    + cbn.
      refine (_ @ !(id_left _)).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 bb) (pr1 φ (pr1 x)))).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb (pr1 η (pr1 x)) (pr1 φ (pr1 x)))
                    (pr1 (pr1 ff (pr1 x)) (pr2 x)))).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb (pr1 η (pr1 x)) (pr1 φ (pr1 x)))
                    (pr1 (pr1 ff (pr1 x)) (pr2 x))
                  @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite !id_right ;
         rewrite functor_id ;
         apply idpath).
    + cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  etrans.
                  {
                    apply maponpaths.
                    etrans.
                    {
                      apply maponpaths.
                      refine (!_).
                      apply (pr1_maponpaths_idtoiso (pr1 ff (pr1 x))).
                    }
                    refine (!_).
                    apply (pr1_idtoiso_concat
                             (functor_total_category_of_set_functor_eq
                                f ff
                                (id₁ (pr1 x) ,, _))).
                  }
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp bb _ _) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id bb _) _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp bb _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber (functor_comp bb _ _) _ @ _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 ((eq_in_set_fiber (functor_comp bb _ _) _ @ _) @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite !id_right ;
         apply idpath).
    + cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         (eq_in_set_fiber
                            (functor_comp bb _ _)
                            _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       _
                       (eq_in_set_fiber
                          (functor_id bb _)
                          _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 bb) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber
                      (functor_comp bb _ _)
                      _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp bb _ _)
                    _
                  @ _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 ((eq_in_set_fiber (functor_comp bb _ _) _ @ _) @ _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite functor_id ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (eq_in_set_fiber
                          (functor_comp dd _ _)
                          _)).
            }
            refine (!_).
            exact (pr1_idtoiso_concat
                     _
                     (eq_in_set_fiber
                        (functor_id dd _)
                        _)).
          }
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp dd _ _)
                    _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 (eq_in_set_fiber
                    (functor_comp dd _ _)
                    _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (pr1 hh _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         _
                         (maponpaths
                            (pr11 (pr1 hh _))
                            (eq_in_set_fiber (functor_id cc _) _))).
              }
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  refine (!_).
                  apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
                }
                refine (!_).
                apply (pr1_idtoiso_concat
                         (eq_in_set_fiber (functor_comp dd _ _) _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (eq_in_set_fiber (functor_comp dd _ _) _ @ _)).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 dd) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat
                   (eq_in_set_fiber (functor_comp dd _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 (eq_in_set_fiber (functor_id dd _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat
                 _
                 (_ @ eq_in_set_fiber (functor_id dd _) _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id cc _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat _ (_ @ eq_in_set_fiber (functor_id cc _) _)).
      }
      apply setcategory_eq_idtoiso.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)).
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    use eq_mor_category_of_set_functor.
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + cbn.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _ @ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply (pr1_maponpaths_idtoiso (pr1 gg _)).
              }
              refine (!_).
              apply (pr1_idtoiso_concat
                       (functor_total_category_of_set_functor_eq
                          g gg
                          (nat_trans_total_category_of_set_functor_data
                             η ff₁ ff₂ ηη x))).
            }
            refine (!_).
            apply (pr1_maponpaths_idtoiso (# (pr1 cc) _)).
          }
          refine (!_).
          apply (pr1_idtoiso_concat (eq_in_set_fiber (functor_comp cc _ _) _)).
        }
        refine (!_).
        apply (pr1_idtoiso_concat _ (eq_in_set_fiber (functor_id cc _) _)).
      }
      etrans.
      {
        refine (!_).
        apply (pr1_idtoiso_concat _ (_ @ eq_in_set_fiber (functor_id cc _) _)).
      }
      apply setcategory_eq_idtoiso.
Time Qed.

Definition functors_into_cat_comprehension
  : disp_psfunctor
      disp_bicat_of_functors_into_cat
      (cod_disp_bicat bicat_of_strict_cats)
      (id_psfunctor bicat_of_strict_cats)
  := functors_into_cat_comprehension_data
     ,,
     is_disp_psfunctor_functors_into_cat_comprehension.



Definition local_opcartesian_functors_into_cat_comprehension
  : local_opcartesian_disp_psfunctor functors_into_cat_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂ p Hp.
  use is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
  use strict_pointwise_opcartesian_is_opcartesian.
  cbn.
  intro x.
  apply is_opcartesian_total_setcategory_of_set_functor.
  cbn.
  apply z_iso_is_z_isomorphism.
Qed.


Definition TODO { A : UU } : A.
Admitted.









Section PullbackFromTotal.
  Context {C₁ C₂ : setcategory}
         {F : C₁ ⟶ C₂}
         {G₁ : C₁ ⟶ cat_of_setcategory}
         {G₂ : C₂ ⟶ cat_of_setcategory}
         (α : G₁ ⟹ F ∙ G₂)
         (Hα : is_nat_z_iso α).

  Section PbMor.
    Context {C₀ : setcategory}
           (P₁ : C₀ ⟶ C₁)
           (P₂ : C₀ ⟶ total_setcategory_of_set_functor G₂)
           (β : P₁ ∙ F ⟹ P₂ ∙ pr1_total_category_of_set_functor G₂)
           (Hβ : is_nat_z_iso β).

    Definition test
      : C₀ ⟶ total_setcategory_of_set_functor G₁.
    Proof.
      use make_functor.
      - use make_functor_data.
        + cbn.
          refine (λ x, P₁ x ,, _).
          apply (pr1 (Hα (P₁ x))).
          apply (# G₂ (pr1 (Hβ x))).
          exact (pr2 (P₂ x)).
        + cbn.
          apply TODO.
      - apply TODO.
    Defined.

    Definition test_pr1
      : test ∙ pr1_total_category_of_set_functor G₁ ⟹ P₁.
    Proof.
      use make_nat_trans.
      - exact (λ _, identity _).
      - intros x y f ; cbn.
        apply TODO.
    Defined.

    Definition test_pr2
      : test ∙ functor_total_category_of_set_functor F α ⟹ P₂.
    Proof.
      use make_nat_trans.
      - refine (λ x, β x ,, _).
        cbn.
        apply TODO.
      - apply TODO.
    Defined.

  End PbMor.
End PullbackFromTotal.

Definition global_cartesian_functors_into_cat_comprehension
  : global_cartesian_disp_psfunctor functors_into_cat_comprehension.
Proof.
  intros C₁ C₂ F G₁ G₂ α Hα.
  use is_pb_to_cartesian_1cell.
  pose (functors_into_cat_cartesian_1cell_is_nat_iso _ Hα) as Hα'.
  cbn in *.
  split.
  - intro x.
    use make_pb_1cell.
    + exact (test α Hα' (pb_cone_pr1 x) (pb_cone_pr2 x) (pr1 (pb_cone_cell x)) TODO).
    + use make_invertible_2cell.
      * exact (test_pr1 α Hα' (pb_cone_pr1 x) (pb_cone_pr2 x) (pr1 (pb_cone_cell x)) TODO).
      * apply is_invertible_2cell_bicat_of_strict_cat.
        cbn.
        apply TODO.
    + use make_invertible_2cell.
      * exact (test_pr2 α Hα' (pb_cone_pr1 x) (pb_cone_pr2 x) (pr1 (pb_cone_cell x)) TODO).
      * apply is_invertible_2cell_bicat_of_strict_cat.
        cbn.
        apply TODO.
    + use nat_trans_eq ; [ apply homset_property | ].
      intro z ; cbn.
      rewrite (functor_id F).
      rewrite !id_left, id_right.
      apply TODO.
  - admit.
Admitted.

(************************************************


    ∫ G₁ ⟶ ∫ G₂
      |       |
      V       V
      C₁ ⟶   C₂

 is a pb

 ************************************************)


Definition functors_into_cat_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_strict_cats
  := disp_bicat_of_functors_into_cat
     ,,
     functors_into_cat_comprehension
     ,,
     functors_into_cat_global_cleaving
     ,,
     global_cartesian_functors_into_cat_comprehension.

Definition is_covariant_functors_into_cat_comprehension_bicat
  : is_covariant functors_into_cat_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact functors_into_cat_local_opcleaving.
  - intro ; intros.
    apply functors_into_cat_is_opcartesian_2cell.
  - intro ; intros.
    apply functors_into_cat_is_opcartesian_2cell.
  - exact local_opcartesian_functors_into_cat_comprehension.
Defined.

Definition functors_into_cat_comprehension_bicat
  : comprehension_bicat
  := _
     ,,
     functors_into_cat_comprehension_bicat_structure
     ,,
     is_covariant_functors_into_cat_comprehension_bicat.
